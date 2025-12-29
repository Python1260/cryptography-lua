local function FromByteAndSize(Byte: number, Size: number)
	local Buffer = buffer.create(Size)
	buffer.fill(Buffer, 0, Byte)
	return Buffer
end

local function ToBigEndian(Buffer: buffer)
	for Index = 0, buffer.len(Buffer) - 1, 4 do
		buffer.writeu32(Buffer, Index, bit32.byteswap(buffer.readu32(Buffer, Index)))
	end
end

local function ConcatenateBuffers(LeftBuffer: buffer, RightBuffer: buffer)
	local LeftBufLen = buffer.len(LeftBuffer)
	local Buffer = buffer.create(LeftBufLen + buffer.len(RightBuffer))

	buffer.copy(Buffer, 0, LeftBuffer)
	buffer.copy(Buffer, LeftBufLen, RightBuffer)

	return Buffer
end

local function XORBuffer(LeftBuffer: buffer, RightBuffer: buffer)
	local Size = math.min(buffer.len(LeftBuffer), buffer.len(RightBuffer))
	local NewBuffer = buffer.create(Size)

	for Index = 0, Size - 1 do
		local LeftValue = buffer.readu8(LeftBuffer, Index)
		local RightValue = buffer.readu8(RightBuffer, Index)
		buffer.writeu8(NewBuffer, Index, bit32.bxor(LeftValue, RightValue))
	end

	return NewBuffer
end

local function ComputeBlockSizedKey(Key: buffer, HashFunction: HashFunction, BlockSizeBytes: number, BigEndian: boolean?): buffer
	local KeyLength = buffer.len(Key)
	if KeyLength > BlockSizeBytes then
		local _, Digest = HashFunction(Key)
		if BigEndian ~= false then
			ToBigEndian(Digest)
		end
		
		local PaddedKey = buffer.create(BlockSizeBytes)
		buffer.copy(PaddedKey, 0, Digest)
		return PaddedKey
	elseif KeyLength < BlockSizeBytes then
		local PaddedKey = buffer.create(BlockSizeBytes)
		buffer.copy(PaddedKey, 0, Key)
		return PaddedKey
	end
	
	return Key
end

local function HMAC(Message: buffer, Key: buffer, HashFunction: HashFunction, BlockSizeBytes: number, BigEndian: boolean?): (string, buffer)
	local BlockSizedKey = ComputeBlockSizedKey(Key, HashFunction, BlockSizeBytes, BigEndian)
	local OuterPaddedKey = XORBuffer(BlockSizedKey, FromByteAndSize(0x5C, BlockSizeBytes))
	local InnerPaddedKey = XORBuffer(BlockSizedKey, FromByteAndSize(0x36, BlockSizeBytes))
	local _, HashedMessageWithInnerKey = HashFunction(ConcatenateBuffers(InnerPaddedKey, Message))

	if BigEndian ~= false then
		ToBigEndian(HashedMessageWithInnerKey)
	end

	local FinalMessage = ConcatenateBuffers(OuterPaddedKey, HashedMessageWithInnerKey)
	return HashFunction(FinalMessage)
end

local KMAC = {}

local ENCODE_LOOKUP = buffer.create(256 * 2) do
	local HexChars = "0123456789abcdef"
	for Byte = 0, 255 do
		local HighNibble = bit32.rshift(Byte, 4)
		local LowNibble = Byte % 16

		local HighChar = string.byte(HexChars, HighNibble + 1)
		local LowChar = string.byte(HexChars, LowNibble + 1)

		local Combined = HighChar + bit32.lshift(LowChar, 8)
		buffer.writeu16(ENCODE_LOOKUP, Byte * 2, Combined)
	end
end

local LOW_ROUND, HIGH_ROUND = buffer.create(96), buffer.create(96) do
	local HighFactorKeccak = 0
	local ShiftRegister = 29
	local function GetNextBit(): number
		local Result = ShiftRegister % 2
		ShiftRegister =  bit32.bxor((ShiftRegister - Result) // 2, 142 * Result)

		return Result
	end

	for Index = 0, 23 do
		local LowValue: number, Multiplier: number = 0, nil

		for _ = 1, 6 do
			Multiplier = if Multiplier then Multiplier * Multiplier * 2 else 1
			LowValue += GetNextBit() * Multiplier
		end

		local HighValue = GetNextBit() * Multiplier
		buffer.writeu32(HIGH_ROUND, Index * 4, HighValue)
		buffer.writeu32(LOW_ROUND, Index * 4, LowValue + HighValue * HighFactorKeccak)
	end
end

local LANES_LOW = buffer.create(100)
local LANES_HIGH = buffer.create(100)
local FUNCTION_NAME = buffer.fromstring("KMAC")
local RESULT = buffer.create(2)

local function Keccak(LanesLow: buffer, LanesHigh: buffer, InputBuffer: buffer, Offset: number, Size: number, BlockSizeInBytes: number): ()
	local QuadWordsQuantity = BlockSizeInBytes // 8
	local RCHigh, RCLow = HIGH_ROUND, LOW_ROUND
	local XOR = bit32.bxor

	for Position = Offset, Offset + Size - 1, BlockSizeInBytes do
		for Index = 0, (QuadWordsQuantity - 1) * 4, 4 do
			local BufferPos = Position + Index * 2

			buffer.writeu32(LanesLow, Index, XOR(
				buffer.readu32(LanesLow, Index),
				buffer.readu32(InputBuffer, BufferPos)
				))

			buffer.writeu32(LanesHigh, Index, XOR(
				buffer.readu32(LanesHigh, Index),
				buffer.readu32(InputBuffer, BufferPos + 4)
				))
		end

		local Lane01Low, Lane01High = buffer.readu32(LanesLow, 0), buffer.readu32(LanesHigh, 0)
		local Lane02Low, Lane02High = buffer.readu32(LanesLow, 4), buffer.readu32(LanesHigh, 4)
		local Lane03Low, Lane03High = buffer.readu32(LanesLow, 8), buffer.readu32(LanesHigh, 8)

		local Lane04Low, Lane04High = buffer.readu32(LanesLow, 12), buffer.readu32(LanesHigh, 12)
		local Lane05Low, Lane05High = buffer.readu32(LanesLow, 16), buffer.readu32(LanesHigh, 16)
		local Lane06Low, Lane06High = buffer.readu32(LanesLow, 20), buffer.readu32(LanesHigh, 20)

		local Lane07Low, Lane07High = buffer.readu32(LanesLow, 24), buffer.readu32(LanesHigh, 24)
		local Lane08Low, Lane08High = buffer.readu32(LanesLow, 28), buffer.readu32(LanesHigh, 28)
		local Lane09Low, Lane09High = buffer.readu32(LanesLow, 32), buffer.readu32(LanesHigh, 32)

		local Lane10Low, Lane10High = buffer.readu32(LanesLow, 36), buffer.readu32(LanesHigh, 36)
		local Lane11Low, Lane11High = buffer.readu32(LanesLow, 40), buffer.readu32(LanesHigh, 40)
		local Lane12Low, Lane12High = buffer.readu32(LanesLow, 44), buffer.readu32(LanesHigh, 44)

		local Lane13Low, Lane13High = buffer.readu32(LanesLow, 48), buffer.readu32(LanesHigh, 48)
		local Lane14Low, Lane14High = buffer.readu32(LanesLow, 52), buffer.readu32(LanesHigh, 52)
		local Lane15Low, Lane15High = buffer.readu32(LanesLow, 56), buffer.readu32(LanesHigh, 56)

		local Lane16Low, Lane16High = buffer.readu32(LanesLow, 60), buffer.readu32(LanesHigh, 60)
		local Lane17Low, Lane17High = buffer.readu32(LanesLow, 64), buffer.readu32(LanesHigh, 64)
		local Lane18Low, Lane18High = buffer.readu32(LanesLow, 68), buffer.readu32(LanesHigh, 68)

		local Lane19Low, Lane19High = buffer.readu32(LanesLow, 72), buffer.readu32(LanesHigh, 72)
		local Lane20Low, Lane20High = buffer.readu32(LanesLow, 76), buffer.readu32(LanesHigh, 76)
		local Lane21Low, Lane21High = buffer.readu32(LanesLow, 80), buffer.readu32(LanesHigh, 80)

		local Lane22Low, Lane22High = buffer.readu32(LanesLow, 84), buffer.readu32(LanesHigh, 84)
		local Lane23Low, Lane23High = buffer.readu32(LanesLow, 88), buffer.readu32(LanesHigh, 88)
		local Lane24Low, Lane24High = buffer.readu32(LanesLow, 92), buffer.readu32(LanesHigh, 92)

		local Lane25Low, Lane25High = buffer.readu32(LanesLow, 96), buffer.readu32(LanesHigh, 96)

		for RoundIndex = 0, 92, 4 do
			local Column1Low, Column1High = XOR(Lane01Low, Lane06Low, Lane11Low, Lane16Low, Lane21Low), XOR(Lane01High, Lane06High, Lane11High, Lane16High, Lane21High)
			local Column2Low, Column2High = XOR(Lane02Low, Lane07Low, Lane12Low, Lane17Low, Lane22Low), XOR(Lane02High, Lane07High, Lane12High, Lane17High, Lane22High)
			local Column3Low, Column3High = XOR(Lane03Low, Lane08Low, Lane13Low, Lane18Low, Lane23Low), XOR(Lane03High, Lane08High, Lane13High, Lane18High, Lane23High)
			local Column4Low, Column4High = XOR(Lane04Low, Lane09Low, Lane14Low, Lane19Low, Lane24Low), XOR(Lane04High, Lane09High, Lane14High, Lane19High, Lane24High)
			local Column5Low, Column5High = XOR(Lane05Low, Lane10Low, Lane15Low, Lane20Low, Lane25Low), XOR(Lane05High, Lane10High, Lane15High, Lane20High, Lane25High)

			local DeltaLow, DeltaHigh = XOR(Column1Low, Column3Low * 2 + Column3High // 2147483648), XOR(Column1High, Column3High * 2 + Column3Low // 2147483648)
			local Temp0Low, Temp0High = XOR(DeltaLow, Lane02Low), XOR(DeltaHigh, Lane02High)
			local Temp1Low, Temp1High = XOR(DeltaLow, Lane07Low), XOR(DeltaHigh, Lane07High)
			local Temp2Low, Temp2High = XOR(DeltaLow, Lane12Low), XOR(DeltaHigh, Lane12High)
			local Temp3Low, Temp3High = XOR(DeltaLow, Lane17Low), XOR(DeltaHigh, Lane17High)
			local Temp4Low, Temp4High = XOR(DeltaLow, Lane22Low), XOR(DeltaHigh, Lane22High)

			Lane02Low = Temp1Low // 1048576 + (Temp1High * 4096); Lane02High = Temp1High // 1048576 + (Temp1Low * 4096)
			Lane07Low = Temp3Low // 524288 + (Temp3High * 8192); Lane07High = Temp3High // 524288 + (Temp3Low * 8192)
			Lane12Low = Temp0Low * 2 + Temp0High // 2147483648; Lane12High = Temp0High * 2 + Temp0Low // 2147483648
			Lane17Low = Temp2Low * 1024 + Temp2High // 4194304; Lane17High = Temp2High * 1024 + Temp2Low // 4194304
			Lane22Low = Temp4Low * 4 + Temp4High // 1073741824; Lane22High = Temp4High * 4 + Temp4Low // 1073741824

			DeltaLow = XOR(Column2Low, Column4Low * 2 + Column4High // 2147483648); DeltaHigh = XOR(Column2High, Column4High * 2 + Column4Low // 2147483648)
			Temp0Low = XOR(DeltaLow, Lane03Low); Temp0High = XOR(DeltaHigh, Lane03High)
			Temp1Low = XOR(DeltaLow, Lane08Low); Temp1High = XOR(DeltaHigh, Lane08High)
			Temp2Low = XOR(DeltaLow, Lane13Low); Temp2High = XOR(DeltaHigh, Lane13High)
			Temp3Low = XOR(DeltaLow, Lane18Low); Temp3High = XOR(DeltaHigh, Lane18High)
			Temp4Low = XOR(DeltaLow, Lane23Low); Temp4High = XOR(DeltaHigh, Lane23High)

			Lane03Low = Temp2Low // 2097152 + (Temp2High * 2048); Lane03High = Temp2High // 2097152 + (Temp2Low * 2048)
			Lane08Low = Temp4Low // 8 + bit32.bor(Temp4High * 536870912, 0); Lane08High = Temp4High // 8 + bit32.bor(Temp4Low * 536870912, 0)
			Lane13Low = Temp1Low * 64 + Temp1High // 67108864; Lane13High = Temp1High * 64 + Temp1Low // 67108864
			Lane18Low = (Temp3Low * 32768) + Temp3High // 131072; Lane18High = (Temp3High * 32768) + Temp3Low // 131072
			Lane23Low = Temp0Low // 4 + bit32.bor(Temp0High * 1073741824, 0); Lane23High = Temp0High // 4 + bit32.bor(Temp0Low * 1073741824, 0)

			DeltaLow = XOR(Column3Low, Column5Low * 2 + Column5High // 2147483648); DeltaHigh = XOR(Column3High, Column5High * 2 + Column5Low // 2147483648)
			Temp0Low = XOR(DeltaLow, Lane04Low); Temp0High = XOR(DeltaHigh, Lane04High)
			Temp1Low = XOR(DeltaLow, Lane09Low); Temp1High = XOR(DeltaHigh, Lane09High)
			Temp2Low = XOR(DeltaLow, Lane14Low); Temp2High = XOR(DeltaHigh, Lane14High)
			Temp3Low = XOR(DeltaLow, Lane19Low); Temp3High = XOR(DeltaHigh, Lane19High)
			Temp4Low = XOR(DeltaLow, Lane24Low); Temp4High = XOR(DeltaHigh, Lane24High)

			Lane04Low = bit32.bor(Temp3Low * 2097152, 0) + Temp3High // 2048; Lane04High = bit32.bor(Temp3High * 2097152, 0) + Temp3Low // 2048
			Lane09Low = bit32.bor(Temp0Low * 268435456, 0) + Temp0High // 16; Lane09High = bit32.bor(Temp0High * 268435456, 0) + Temp0Low // 16
			Lane14Low = bit32.bor(Temp2Low * 33554432, 0) + Temp2High // 128; Lane14High = bit32.bor(Temp2High * 33554432, 0) + Temp2Low // 128
			Lane19Low = Temp4Low // 256 + bit32.bor(Temp4High * 16777216, 0); Lane19High = Temp4High // 256 + bit32.bor(Temp4Low * 16777216, 0)
			Lane24Low = Temp1Low // 512 + bit32.bor(Temp1High * 8388608, 0); Lane24High = Temp1High // 512 + bit32.bor(Temp1Low * 8388608, 0)
			DeltaLow = XOR(Column4Low, Column1Low * 2 + Column1High // 2147483648); DeltaHigh = XOR(Column4High, Column1High * 2 + Column1Low // 2147483648)

			Temp0Low = XOR(DeltaLow, Lane05Low); Temp0High = XOR(DeltaHigh, Lane05High)
			Temp1Low = XOR(DeltaLow, Lane10Low); Temp1High = XOR(DeltaHigh, Lane10High)
			Temp2Low = XOR(DeltaLow, Lane15Low); Temp2High = XOR(DeltaHigh, Lane15High)
			Temp3Low = XOR(DeltaLow, Lane20Low); Temp3High = XOR(DeltaHigh, Lane20High)
			Temp4Low = XOR(DeltaLow, Lane25Low); Temp4High = XOR(DeltaHigh, Lane25High)

			Lane05Low = (Temp4Low * 16384) + Temp4High // 262144; Lane05High = (Temp4High * 16384) + Temp4Low // 262144
			Lane10Low = bit32.bor(Temp1Low * 1048576, 0) + Temp1High // 4096; Lane10High = bit32.bor(Temp1High * 1048576, 0) + Temp1Low // 4096
			Lane15Low = Temp3Low * 256 + Temp3High // 16777216; Lane15High = Temp3High * 256 + Temp3Low // 16777216
			Lane20Low = bit32.bor(Temp0Low * 134217728, 0) + Temp0High // 32; Lane20High = bit32.bor(Temp0High * 134217728, 0) + Temp0Low // 32
			Lane25Low = Temp2Low // 33554432 + Temp2High * 128; Lane25High = Temp2High // 33554432 + Temp2Low * 128

			DeltaLow = XOR(Column5Low, Column2Low * 2 + Column2High // 2147483648); DeltaHigh = XOR(Column5High, Column2High * 2 + Column2Low // 2147483648)
			Temp1Low = XOR(DeltaLow, Lane06Low); Temp1High = XOR(DeltaHigh, Lane06High)
			Temp2Low = XOR(DeltaLow, Lane11Low); Temp2High = XOR(DeltaHigh, Lane11High)
			Temp3Low = XOR(DeltaLow, Lane16Low); Temp3High = XOR(DeltaHigh, Lane16High)
			Temp4Low = XOR(DeltaLow, Lane21Low); Temp4High = XOR(DeltaHigh, Lane21High)
			Lane06Low = Temp2Low * 8 + Temp2High // 536870912; Lane06High = Temp2High * 8 + Temp2Low // 536870912
			Lane11Low = (Temp4Low * 262144) + Temp4High // 16384; Lane11High = (Temp4High * 262144) + Temp4Low // 16384
			Lane16Low = Temp1Low // 268435456 + Temp1High * 16; Lane16High = Temp1High // 268435456 + Temp1Low * 16
			Lane21Low = Temp3Low // 8388608 + Temp3High * 512; Lane21High = Temp3High // 8388608 + Temp3Low * 512
			Lane01Low = XOR(DeltaLow, Lane01Low); Lane01High = XOR(DeltaHigh, Lane01High)

			Lane01Low, Lane02Low, Lane03Low, Lane04Low, Lane05Low =  XOR(Lane01Low, bit32.band(-1 - Lane02Low, Lane03Low)),  XOR(Lane02Low, bit32.band(-1 - Lane03Low, Lane04Low)),  XOR(Lane03Low, bit32.band(-1 - Lane04Low, Lane05Low)),  XOR(Lane04Low, bit32.band(-1 - Lane05Low, Lane01Low)),  XOR(Lane05Low, bit32.band(-1 - Lane01Low, Lane02Low))
			Lane01High, Lane02High, Lane03High, Lane04High, Lane05High =  XOR(Lane01High, bit32.band(-1 - Lane02High, Lane03High)),  XOR(Lane02High, bit32.band(-1 - Lane03High, Lane04High)),  XOR(Lane03High, bit32.band(-1 - Lane04High, Lane05High)),  XOR(Lane04High, bit32.band(-1 - Lane05High, Lane01High)),  XOR(Lane05High, bit32.band(-1 - Lane01High, Lane02High))
			Lane06Low, Lane07Low, Lane08Low, Lane09Low, Lane10Low =  XOR(Lane09Low, bit32.band(-1 - Lane10Low, Lane06Low)),  XOR(Lane10Low, bit32.band(-1 - Lane06Low, Lane07Low)),  XOR(Lane06Low, bit32.band(-1 - Lane07Low, Lane08Low)),  XOR(Lane07Low, bit32.band(-1 - Lane08Low, Lane09Low)),  XOR(Lane08Low, bit32.band(-1 - Lane09Low, Lane10Low))
			Lane06High, Lane07High, Lane08High, Lane09High, Lane10High =  XOR(Lane09High, bit32.band(-1 - Lane10High, Lane06High)),  XOR(Lane10High, bit32.band(-1 - Lane06High, Lane07High)),  XOR(Lane06High, bit32.band(-1 - Lane07High, Lane08High)),  XOR(Lane07High, bit32.band(-1 - Lane08High, Lane09High)),  XOR(Lane08High, bit32.band(-1 - Lane09High, Lane10High))
			Lane11Low, Lane12Low, Lane13Low, Lane14Low, Lane15Low =  XOR(Lane12Low, bit32.band(-1 - Lane13Low, Lane14Low)),  XOR(Lane13Low, bit32.band(-1 - Lane14Low, Lane15Low)),  XOR(Lane14Low, bit32.band(-1 - Lane15Low, Lane11Low)),  XOR(Lane15Low, bit32.band(-1 - Lane11Low, Lane12Low)),  XOR(Lane11Low, bit32.band(-1 - Lane12Low, Lane13Low))
			Lane11High, Lane12High, Lane13High, Lane14High, Lane15High =  XOR(Lane12High, bit32.band(-1 - Lane13High, Lane14High)),  XOR(Lane13High, bit32.band(-1 - Lane14High, Lane15High)),  XOR(Lane14High, bit32.band(-1 - Lane15High, Lane11High)),  XOR(Lane15High, bit32.band(-1 - Lane11High, Lane12High)),  XOR(Lane11High, bit32.band(-1 - Lane12High, Lane13High))
			Lane16Low, Lane17Low, Lane18Low, Lane19Low, Lane20Low =  XOR(Lane20Low, bit32.band(-1 - Lane16Low, Lane17Low)),  XOR(Lane16Low, bit32.band(-1 - Lane17Low, Lane18Low)),  XOR(Lane17Low, bit32.band(-1 - Lane18Low, Lane19Low)),  XOR(Lane18Low, bit32.band(-1 - Lane19Low, Lane20Low)),  XOR(Lane19Low, bit32.band(-1 - Lane20Low, Lane16Low))
			Lane16High, Lane17High, Lane18High, Lane19High, Lane20High =  XOR(Lane20High, bit32.band(-1 - Lane16High, Lane17High)),  XOR(Lane16High, bit32.band(-1 - Lane17High, Lane18High)),  XOR(Lane17High, bit32.band(-1 - Lane18High, Lane19High)),  XOR(Lane18High, bit32.band(-1 - Lane19High, Lane20High)),  XOR(Lane19High, bit32.band(-1 - Lane20High, Lane16High))
			Lane21Low, Lane22Low, Lane23Low, Lane24Low, Lane25Low =  XOR(Lane23Low, bit32.band(-1 - Lane24Low, Lane25Low)),  XOR(Lane24Low, bit32.band(-1 - Lane25Low, Lane21Low)),  XOR(Lane25Low, bit32.band(-1 - Lane21Low, Lane22Low)),  XOR(Lane21Low, bit32.band(-1 - Lane22Low, Lane23Low)),  XOR(Lane22Low, bit32.band(-1 - Lane23Low, Lane24Low))
			Lane21High, Lane22High, Lane23High, Lane24High, Lane25High =  XOR(Lane23High, bit32.band(-1 - Lane24High, Lane25High)),  XOR(Lane24High, bit32.band(-1 - Lane25High, Lane21High)),  XOR(Lane25High, bit32.band(-1 - Lane21High, Lane22High)),  XOR(Lane21High, bit32.band(-1 - Lane22High, Lane23High)),  XOR(Lane22High, bit32.band(-1 - Lane23High, Lane24High))

			Lane01Low =  XOR(Lane01Low, buffer.readu32(RCLow, RoundIndex))
			Lane01High = XOR(Lane01High, buffer.readu32(RCHigh, RoundIndex))
		end

		buffer.writeu32(LanesLow, 0, Lane01Low); buffer.writeu32(LanesHigh, 0, Lane01High)
		buffer.writeu32(LanesLow, 4, Lane02Low); buffer.writeu32(LanesHigh, 4, Lane02High)
		buffer.writeu32(LanesLow, 8, Lane03Low); buffer.writeu32(LanesHigh, 8, Lane03High)
		buffer.writeu32(LanesLow, 12, Lane04Low); buffer.writeu32(LanesHigh, 12, Lane04High)
		buffer.writeu32(LanesLow, 16, Lane05Low); buffer.writeu32(LanesHigh, 16, Lane05High)
		buffer.writeu32(LanesLow, 20, Lane06Low); buffer.writeu32(LanesHigh, 20, Lane06High)
		buffer.writeu32(LanesLow, 24, Lane07Low); buffer.writeu32(LanesHigh, 24, Lane07High)
		buffer.writeu32(LanesLow, 28, Lane08Low); buffer.writeu32(LanesHigh, 28, Lane08High)
		buffer.writeu32(LanesLow, 32, Lane09Low); buffer.writeu32(LanesHigh, 32, Lane09High)
		buffer.writeu32(LanesLow, 36, Lane10Low); buffer.writeu32(LanesHigh, 36, Lane10High)
		buffer.writeu32(LanesLow, 40, Lane11Low); buffer.writeu32(LanesHigh, 40, Lane11High)
		buffer.writeu32(LanesLow, 44, Lane12Low); buffer.writeu32(LanesHigh, 44, Lane12High)
		buffer.writeu32(LanesLow, 48, Lane13Low); buffer.writeu32(LanesHigh, 48, Lane13High)
		buffer.writeu32(LanesLow, 52, Lane14Low); buffer.writeu32(LanesHigh, 52, Lane14High)
		buffer.writeu32(LanesLow, 56, Lane15Low); buffer.writeu32(LanesHigh, 56, Lane15High)
		buffer.writeu32(LanesLow, 60, Lane16Low); buffer.writeu32(LanesHigh, 60, Lane16High)
		buffer.writeu32(LanesLow, 64, Lane17Low); buffer.writeu32(LanesHigh, 64, Lane17High)
		buffer.writeu32(LanesLow, 68, Lane18Low); buffer.writeu32(LanesHigh, 68, Lane18High)
		buffer.writeu32(LanesLow, 72, Lane19Low); buffer.writeu32(LanesHigh, 72, Lane19High)
		buffer.writeu32(LanesLow, 76, Lane20Low); buffer.writeu32(LanesHigh, 76, Lane20High)
		buffer.writeu32(LanesLow, 80, Lane21Low); buffer.writeu32(LanesHigh, 80, Lane21High)
		buffer.writeu32(LanesLow, 84, Lane22Low); buffer.writeu32(LanesHigh, 84, Lane22High)
		buffer.writeu32(LanesLow, 88, Lane23Low); buffer.writeu32(LanesHigh, 88, Lane23High)
		buffer.writeu32(LanesLow, 92, Lane24Low); buffer.writeu32(LanesHigh, 92, Lane24High)
		buffer.writeu32(LanesLow, 96, Lane25Low); buffer.writeu32(LanesHigh, 96, Lane25High)
	end
end

local function LeftEncode(Value: number): buffer
	if Value == 0 then
		buffer.writeu8(RESULT, 0, 1)
		buffer.writeu8(RESULT, 1, 0)
		
		return RESULT
	end

	local ByteLength = 1
	if Value > 0xFF then
		if Value > 0xFFFF then
			if Value > 0xFFFFFF then
				ByteLength = 4
			else
				ByteLength = 3
			end
		else
			ByteLength = 2
		end
	end

	local Result = buffer.create(ByteLength + 1)
	buffer.writeu8(Result, 0, ByteLength)

	if ByteLength == 1 then
		buffer.writeu8(Result, 1, Value)
	elseif ByteLength == 2 then
		buffer.writeu8(Result, 1, bit32.rshift(Value, 8))
		buffer.writeu8(Result, 2, bit32.band(Value, 0xFF))
	elseif ByteLength == 3 then
		buffer.writeu8(Result, 1, bit32.rshift(Value, 16))
		buffer.writeu8(Result, 2, bit32.band(bit32.rshift(Value, 8), 0xFF))
		buffer.writeu8(Result, 3, bit32.band(Value, 0xFF))
	else
		buffer.writeu8(Result, 1, bit32.rshift(Value, 24))
		buffer.writeu8(Result, 2, bit32.band(bit32.rshift(Value, 16), 0xFF))
		buffer.writeu8(Result, 3, bit32.band(bit32.rshift(Value, 8), 0xFF))
		buffer.writeu8(Result, 4, bit32.band(Value, 0xFF))
	end

	return Result
end

local function RightEncode(Value: number): buffer
	if Value == 0 then
		buffer.writeu8(RESULT, 0, 0)
		buffer.writeu8(RESULT, 1, 1)
		
		return RESULT
	end

	local ByteLength = 1
	if Value > 0xFF then
		if Value > 0xFFFF then
			if Value > 0xFFFFFF then
				ByteLength = 4
			else
				ByteLength = 3
			end
		else
			ByteLength = 2
		end
	end

	local Result = buffer.create(ByteLength + 1)
	buffer.writeu8(Result, ByteLength, ByteLength)

	if ByteLength == 1 then
		buffer.writeu8(Result, 0, Value)
	elseif ByteLength == 2 then
		buffer.writeu8(Result, 0, bit32.rshift(Value, 8))
		buffer.writeu8(Result, 1, bit32.band(Value, 0xFF))
	elseif ByteLength == 3 then
		buffer.writeu8(Result, 0, bit32.rshift(Value, 16))
		buffer.writeu8(Result, 1, bit32.band(bit32.rshift(Value, 8), 0xFF))
		buffer.writeu8(Result, 2, bit32.band(Value, 0xFF))
	else
		buffer.writeu8(Result, 0, bit32.rshift(Value, 24))
		buffer.writeu8(Result, 1, bit32.band(bit32.rshift(Value, 16), 0xFF))
		buffer.writeu8(Result, 2, bit32.band(bit32.rshift(Value, 8), 0xFF))
		buffer.writeu8(Result, 3, bit32.band(Value, 0xFF))
	end

	return Result
end

local function EncodeString(Data: buffer): buffer
	local DataLength = buffer.len(Data)
	
	local LengthEncoding = LeftEncode(DataLength * 8)
	local LengthEncodingSize = buffer.len(LengthEncoding)
	
	local Result = buffer.create(LengthEncodingSize + DataLength)

	buffer.copy(Result, 0, LengthEncoding, 0, LengthEncodingSize)
	buffer.copy(Result, LengthEncodingSize, Data, 0, DataLength)

	return Result
end

local function Bytepad(Data: buffer, Rate: number): buffer
	local DataLength = buffer.len(Data)
	
	local RateEncoding = LeftEncode(Rate)
	local RateEncodingSize = buffer.len(RateEncoding)
	
	local TotalPrePadLength = RateEncodingSize + DataLength
	local PadLength = Rate - (TotalPrePadLength % Rate)
	if PadLength == Rate then
		PadLength = 0
	end

	local Result = buffer.create(TotalPrePadLength + PadLength)
	buffer.copy(Result, 0, RateEncoding, 0, RateEncodingSize)
	buffer.copy(Result, RateEncodingSize, Data, 0, DataLength)

	return Result
end

local function CSHAKE(Output: buffer, CustomBuffer: buffer?, Data: buffer, RateBytes: number): ()	
	buffer.fill(LANES_LOW, 0, 0, 100)
	buffer.fill(LANES_HIGH, 0, 0, 100)

	local LanesLow = LANES_LOW
	local LanesHigh = LANES_HIGH

	local OutputBytes = buffer.len(Output)

	local EncodedFunctionName = EncodeString(FUNCTION_NAME)
	local EncodedFunctionNameSize = buffer.len(EncodedFunctionName)

	local PrefixData: buffer
	if CustomBuffer then
		local EncodedCustomization = EncodeString(CustomBuffer)
		local EncodedCustomizationSize = buffer.len(EncodedCustomization)
		PrefixData = buffer.create(EncodedFunctionNameSize + EncodedCustomizationSize)
		buffer.copy(PrefixData, 0, EncodedFunctionName, 0, EncodedFunctionNameSize)
		buffer.copy(PrefixData, EncodedFunctionNameSize, EncodedCustomization, 0, EncodedCustomizationSize)
	else
		PrefixData = EncodedFunctionName
	end

	local BytepaddedPrefix = Bytepad(PrefixData, RateBytes)
	local BytepaddedPrefixSize = buffer.len(BytepaddedPrefix)
	local DataSize = buffer.len(Data)
	local TotalInputSize = BytepaddedPrefixSize + DataSize

	local PaddedLength = TotalInputSize + 1
	local Remainder = PaddedLength % RateBytes
	if Remainder ~= 0 then
		PaddedLength += (RateBytes - Remainder)
	end

	local PaddedMessage = buffer.create(PaddedLength)
	buffer.copy(PaddedMessage, 0, BytepaddedPrefix, 0, BytepaddedPrefixSize)
	buffer.copy(PaddedMessage, BytepaddedPrefixSize, Data, 0, DataSize)

	local DomainSeparator = 0x04
	if PaddedLength - TotalInputSize == 1 then
		buffer.writeu8(PaddedMessage, TotalInputSize, bit32.bor(DomainSeparator, 0x80))
	else
		buffer.writeu8(PaddedMessage, TotalInputSize, DomainSeparator)
		if PaddedLength - TotalInputSize > 2 then
			buffer.fill(PaddedMessage, TotalInputSize + 1, 0, PaddedLength - TotalInputSize - 2)
		end
		buffer.writeu8(PaddedMessage, PaddedLength - 1, 0x80)
	end

	Keccak(LanesLow, LanesHigh, PaddedMessage, 0, PaddedLength, RateBytes)

	local OutputOffset = 0
	local ZeroBuffer = buffer.create(RateBytes)

	while OutputOffset < OutputBytes do
		local BytesThisRound = math.min(RateBytes, OutputBytes - OutputOffset)

		for ByteIndex = 0, BytesThisRound - 1 do
			local AbsoluteIndex = OutputOffset + ByteIndex
			if AbsoluteIndex < OutputBytes then
				local Lane = ByteIndex // 8
				local ByteInLane = ByteIndex % 8
				local LaneOffset = Lane * 4

				local Value
				if ByteInLane < 4 then
					Value = bit32.extract(buffer.readu32(LanesLow, LaneOffset), ByteInLane * 8, 8)
				else
					Value = bit32.extract(buffer.readu32(LanesHigh, LaneOffset), (ByteInLane - 4) * 8, 8)
				end
				buffer.writeu8(Output, AbsoluteIndex, Value)
			end
		end

		OutputOffset += BytesThisRound

		if OutputOffset < OutputBytes then
			Keccak(LanesLow, LanesHigh, ZeroBuffer, 0, RateBytes, RateBytes)
		end
	end
end

function KMAC.KMAC128(Data: buffer, Key: buffer, Output: buffer, CustomBuffer: buffer?): (string, buffer)
	local OutputBytes = buffer.len(Output)

	local EncodedKey = EncodeString(Key)
	local BytepaddedKey = Bytepad(EncodedKey, 168)

	local BytepaddedKeySize = buffer.len(BytepaddedKey)
	local DataSize = buffer.len(Data)

	local RightEncodedLength = RightEncode(OutputBytes * 8)
	local RightEncodedLengthSize = buffer.len(RightEncodedLength)

	local Hex = buffer.create(OutputBytes * 2)
	local Lookup = ENCODE_LOOKUP

	local Leftover = OutputBytes % 8
	local HexCursor = 0

	local CombinedData = buffer.create(BytepaddedKeySize + DataSize + RightEncodedLengthSize)
	buffer.copy(CombinedData, 0, BytepaddedKey, 0, BytepaddedKeySize)
	buffer.copy(CombinedData, BytepaddedKeySize, Data, 0, DataSize)
	buffer.copy(CombinedData, BytepaddedKeySize + DataSize, RightEncodedLength, 0, RightEncodedLengthSize)

	CSHAKE(Output, CustomBuffer, CombinedData, 168)

	for Index = 0, OutputBytes - Leftover - 1, 8 do
		local Hex1 = buffer.readu16(Lookup, buffer.readu8(Output, Index) * 2)
		local Hex2 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 1) * 2)
		local Hex3 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 2) * 2)
		local Hex4 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 3) * 2)
		local Hex5 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 4) * 2)
		local Hex6 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 5) * 2)
		local Hex7 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 6) * 2)
		local Hex8 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 7) * 2)

		buffer.writeu16(Hex, HexCursor, Hex1)
		buffer.writeu16(Hex, HexCursor + 2, Hex2)
		buffer.writeu16(Hex, HexCursor + 4, Hex3)
		buffer.writeu16(Hex, HexCursor + 6, Hex4)
		buffer.writeu16(Hex, HexCursor + 8, Hex5)
		buffer.writeu16(Hex, HexCursor + 10, Hex6)
		buffer.writeu16(Hex, HexCursor + 12, Hex7)
		buffer.writeu16(Hex, HexCursor + 14, Hex8)

		HexCursor += 16
	end

	for Index = OutputBytes - Leftover, OutputBytes - 1 do
		local HexPair = buffer.readu16(Lookup, buffer.readu8(Output, Index) * 2)
		buffer.writeu16(Hex, HexCursor, HexPair)
		HexCursor += 2
	end

	return buffer.tostring(Hex), Output
end

function KMAC.KMAC256(Data: buffer, Key: buffer, Output: buffer, CustomBuffer: buffer?): (string, buffer)
	local OutputBytes = buffer.len(Output)

	local EncodedKey = EncodeString(Key)
	local BytepaddedKey = Bytepad(EncodedKey, 136)

	local BytepaddedKeySize = buffer.len(BytepaddedKey)
	local DataSize = buffer.len(Data)

	local RightEncodedLength = RightEncode(OutputBytes * 8)
	local RightEncodedLengthSize = buffer.len(RightEncodedLength)

	local Hex = buffer.create(OutputBytes * 2)
	local Lookup = ENCODE_LOOKUP

	local Leftover = OutputBytes % 8
	local HexCursor = 0

	local CombinedData = buffer.create(BytepaddedKeySize + DataSize + RightEncodedLengthSize)
	buffer.copy(CombinedData, 0, BytepaddedKey, 0, BytepaddedKeySize)
	buffer.copy(CombinedData, BytepaddedKeySize, Data, 0, DataSize)
	buffer.copy(CombinedData, BytepaddedKeySize + DataSize, RightEncodedLength, 0, RightEncodedLengthSize)

	CSHAKE(Output, CustomBuffer, CombinedData, 136)

	for Index = 0, OutputBytes - Leftover - 1, 8 do
		local Hex1 = buffer.readu16(Lookup, buffer.readu8(Output, Index) * 2)
		local Hex2 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 1) * 2)
		local Hex3 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 2) * 2)
		local Hex4 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 3) * 2)
		local Hex5 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 4) * 2)
		local Hex6 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 5) * 2)
		local Hex7 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 6) * 2)
		local Hex8 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 7) * 2)

		buffer.writeu16(Hex, HexCursor, Hex1)
		buffer.writeu16(Hex, HexCursor + 2, Hex2)
		buffer.writeu16(Hex, HexCursor + 4, Hex3)
		buffer.writeu16(Hex, HexCursor + 6, Hex4)
		buffer.writeu16(Hex, HexCursor + 8, Hex5)
		buffer.writeu16(Hex, HexCursor + 10, Hex6)
		buffer.writeu16(Hex, HexCursor + 12, Hex7)
		buffer.writeu16(Hex, HexCursor + 14, Hex8)

		HexCursor += 16
	end

	for Index = OutputBytes - Leftover, OutputBytes - 1 do
		local HexPair = buffer.readu16(Lookup, buffer.readu8(Output, Index) * 2)
		buffer.writeu16(Hex, HexCursor, HexPair)
		HexCursor += 2
	end

	return buffer.tostring(Hex), Output
end

local FORMAT_STRING = string.rep("%08x", 4)

local OFFSETS = table.create(64)

local CONSTANTS = {
	0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
	0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
	0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
	0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
	0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
	0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
	0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
	0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
}

local SHIFTS = {
	7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
	5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
	4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
	6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
}

local function PreProcess(Contents: buffer): (buffer, number)
	local ContentLength = buffer.len(Contents)
	local BitLength = ContentLength * 8

	local Padding = (56 - ((ContentLength + 1) % 64)) % 64

	local NewContentLength = ContentLength + 1 + Padding + 8
	local NewContent = buffer.create(NewContentLength)

	buffer.copy(NewContent, 0, Contents)

	buffer.writeu8(NewContent, ContentLength, 0x80)

	local LengthOffset = ContentLength + 1 + Padding
	for Index = 0, 7 do
		local Byte = BitLength % 256
		buffer.writeu8(NewContent, LengthOffset + Index, Byte)
		BitLength = bit32.rshift(BitLength, 8)	
	end

	return NewContent, NewContentLength
end

local function DigestBlocks(Blocks: buffer, Length: number): (number, number, number, number)
	local A, B, C, D = 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476

	local Offsets = OFFSETS
	local Constants = CONSTANTS
	local Shifts = SHIFTS

	for Offset = 0, Length - 1, 64 do
		for WordIndex = 0, 15 do
			local BlockOffset = Offset + WordIndex * 4
			local Word = buffer.readu32(Blocks, BlockOffset)
			Offsets[WordIndex + 1] = Word
		end

		local OldA, OldB, OldC, OldD = A, B, C, D
		local Temp, Func = 0, 0
		for Round = 0, 15 do
			local Chunk = Offsets[Round + 1]
			Func = bit32.bxor(OldD, bit32.band(OldB, bit32.bxor(OldC, OldD)))
			Temp = OldD
			OldD = OldC
			OldC = OldB

			OldB = OldB + bit32.lrotate(OldA + Func + Constants[Round + 1] + Chunk, Shifts[Round + 1])
			OldA = Temp
		end

		for Round = 16, 31 do
			local Chunk = Offsets[(5 * Round + 1) % 16 + 1]
			Func = bit32.bxor(OldC, bit32.band(OldD, bit32.bxor(OldB, OldC)))
			Temp = OldD
			OldD = OldC
			OldC = OldB
			OldB = OldB + bit32.lrotate(OldA + Func + Constants[Round + 1] + Chunk, Shifts[Round + 1])
			OldA = Temp
		end

		for Round = 32, 47 do
			local Chunk = Offsets[(3 * Round + 5) % 16 + 1]
			Func = bit32.bxor(OldB, OldC, OldD)
			Temp = OldD
			OldD = OldC
			OldC = OldB
			OldB = OldB + bit32.lrotate(OldA + Func + Constants[Round + 1] + Chunk, Shifts[Round + 1])
			OldA = Temp
		end

		for Round = 48, 63 do
			local Chunk = Offsets[(7 * Round) % 16 + 1]
			Func = bit32.bxor(OldC, bit32.bor(OldB, bit32.bnot(OldD)))
			Temp = OldD
			OldD = OldC
			OldC = OldB
			OldB = OldB + bit32.lrotate(OldA + Func + Constants[Round + 1] + Chunk, Shifts[Round + 1])
			OldA = Temp
		end

		A = bit32.bor(OldA + A, 0)
		B = bit32.bor(OldB + B, 0)
		C = bit32.bor(OldC + C, 0)
		D = bit32.bor(OldD + D, 0)
	end

	return bit32.byteswap(A), bit32.byteswap(B), bit32.byteswap(C), bit32.byteswap(D)
end

local function MD5(Message: buffer, Salt: buffer?): (string, buffer)
	if Salt and buffer.len(Salt) > 0 then
		local MessageWithSalt = buffer.create(buffer.len(Message) + buffer.len(Salt))
		buffer.copy(MessageWithSalt, 0, Message)
		buffer.copy(MessageWithSalt, buffer.len(Message), Salt)
		Message = MessageWithSalt
	end

	local ProcessedMessage, Length = PreProcess(Message)

	local A, B, C, D = DigestBlocks(ProcessedMessage, Length)
	local Digest = buffer.create(16)
	
	buffer.writeu32(Digest, 0, A)
	buffer.writeu32(Digest, 4, B)
	buffer.writeu32(Digest, 8, C)
	buffer.writeu32(Digest, 12, D)

	return string.format(FORMAT_STRING, A, B, C, D), Digest
end

local FORMAT_STRING = string.rep("%08x", 5)

local OFFSETS = buffer.create(320)

local function PreProcess(Contents: buffer): (buffer, number)
	local ContentLength = buffer.len(Contents)
	local Padding = (64 - ((ContentLength + 9) % 64)) % 64

	local NewContentLength = ContentLength + 1 + Padding + 8
	local NewContent = buffer.create(NewContentLength)
	buffer.copy(NewContent, 0, Contents)
	buffer.writeu8(NewContent, ContentLength, 128)

	local Length8 = ContentLength * 8
	for Index = 7, 0, -1 do
		local Remainder = Length8 % 256
		buffer.writeu8(NewContent, Index + ContentLength + 1 + Padding, Remainder)
		Length8 = (Length8 - Remainder) / 256
	end

	return NewContent, NewContentLength
end

local function DigestBlocks(Blocks: buffer, Length: number): (number, number, number, number, number)
	local A, B, C, D, E = 0x67452301, 0xefcdaB89, 0x98badcfe, 0x10325476, 0xc3d2e1f0
	local Offsets = OFFSETS

	for Offset = 0, Length - 1, 64 do
		for BlockIndex = 0, 60, 4 do
			buffer.writeu32(Offsets, BlockIndex, bit32.byteswap(buffer.readu32(Blocks, Offset + BlockIndex)))
		end

		for Index = 64, 316, 4 do
			buffer.writeu32(Offsets, Index, bit32.lrotate(bit32.bxor(
				buffer.readu32(Offsets, Index - 12),
				buffer.readu32(Offsets, Index - 32),
				buffer.readu32(Offsets, Index - 56),
				buffer.readu32(Offsets, Index - 64)
			), 1))
		end

		local H1, H2, H3, H4, H5 = A, B, C, D, E
		
		local Temp
		for Round = 0, 19 do
			Temp = bit32.lrotate(H1, 5) +
				bit32.band(H2, H3) + bit32.band(-1 - H2, H4) +
				H5 + 0x5a827999 +
				buffer.readu32(Offsets, Round * 4)
			
			H5, H4, H3, H2, H1 = H4, H3, bit32.lrotate(H2, 30), H1, Temp
		end
		
		for Round = 20, 39 do
			Temp = bit32.lrotate(H1, 5) +
				bit32.bxor(H2, H3, H4) +
				H5 + 0x6ed9eba1 +
				buffer.readu32(Offsets, Round * 4)
			
			H5, H4, H3, H2, H1 = H4, H3, bit32.lrotate(H2, 30), H1, Temp
		end
		
		for Round = 40, 59 do
			Temp = bit32.lrotate(H1, 5) +
				bit32.band(H4, H3) + bit32.band(H2, bit32.bxor(H4, H3)) +
				H5 + 0x8f1bbcdc +
				buffer.readu32(Offsets, Round * 4)
			
			H5, H4, H3, H2, H1 = H4, H3, bit32.lrotate(H2, 30), H1, Temp
		end
		
		for Round = 60, 79 do
			Temp = bit32.lrotate(H1, 5) +
				bit32.bxor(H2, H3, H4) +
				H5 + 0xca62c1d6 +
				buffer.readu32(Offsets, Round * 4)
			
			H5, H4, H3, H2, H1 = H4, H3, bit32.lrotate(H2, 30), H1, Temp
		end

		A = bit32.bor(A + H1, 0)
		B = bit32.bor(B + H2, 0)
		C = bit32.bor(C + H3, 0)
		D = bit32.bor(D + H4, 0)
		E = bit32.bor(E + H5, 0)
	end

	return A, B, C, D, E
end

local function SHA1(Message: buffer, Salt: buffer?): string
	if Salt and buffer.len(Salt) > 0 then
		local MessageWithSalt = buffer.create(buffer.len(Message) + buffer.len(Salt))

		buffer.copy(MessageWithSalt, 0, Message)
		buffer.copy(MessageWithSalt, buffer.len(Message), Salt)

		Message = MessageWithSalt
	end

	local ProcessedMessage, Length = PreProcess(Message)
	return string.format(FORMAT_STRING, DigestBlocks(ProcessedMessage, Length))
end

local FORMAT_STRING = string.rep("%08x", 7)

local CONSTANTS = buffer.create(256) do -- CONSTANTS = k
	local RoundConstants = {
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
		0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
		0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
		0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
		0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
		0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
		0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
	}

	for Index, Constant in ipairs(RoundConstants) do
		local BufferOffset = (Index - 1) * 4
		buffer.writeu32(CONSTANTS, BufferOffset, Constant)
	end
end

local function PreProcess(Contents: buffer): (buffer, number)
	local ContentLength = buffer.len(Contents)
	local Padding = -(ContentLength + 9) % 64

	local NewContentLength = ContentLength + 1 + Padding + 8
	local NewContent = buffer.create(NewContentLength)
	buffer.copy(NewContent, 0, Contents)
	buffer.writeu8(NewContent, ContentLength, 128)
	local Length8 = ContentLength * 8
	for Index = 7, 0, -1 do
		local Remainder = Length8 % 256
		buffer.writeu8(NewContent, Index + ContentLength + 1 + Padding, Remainder)
		Length8 = (Length8 - Remainder) / 256
	end

	return NewContent, NewContentLength
end

local OFFSETS = buffer.create(256)
local function DigestBlocks(Blocks: buffer, Length: number): (number, number, number, number, number, number, number)
	local A, B, C, D = 0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939
	local E, F, G, H = 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4

	local Offsets = OFFSETS
	local Constants = CONSTANTS

	for Offset = 0, Length - 1, 64 do
		for BlockIndex = 0, 60, 4 do
			buffer.writeu32(Offsets, BlockIndex, bit32.byteswap(buffer.readu32(Blocks, Offset + BlockIndex)))
		end

		for Index = 64, 252, 4 do
			local Sub15 = buffer.readu32(Offsets, Index - 60)
			local S0 = bit32.bxor(bit32.rrotate(Sub15, 7), bit32.rrotate(Sub15, 18), bit32.rshift(Sub15, 3))

			local Sub2 = buffer.readu32(Offsets, Index - 8)
			local S1 = bit32.bxor(bit32.rrotate(Sub2, 17), bit32.rrotate(Sub2, 19), bit32.rshift(Sub2, 10))

			local Sub7, Sub16 = buffer.readu32(Offsets, Index - 28), buffer.readu32(Offsets, Index - 64)
			buffer.writeu32(Offsets, Index, (Sub16 + S0 + Sub7 + S1))
		end

		local OldA, OldB, OldC, OldD, OldE, OldF, OldG, OldH = A, B, C, D, E, F, G, H

		for BufferIndex = 0, 252, 4 do
			local S1 = bit32.bxor(bit32.rrotate(E, 6), bit32.rrotate(E, 11), bit32.rrotate(E, 25))
			local Ch = bit32.bxor(bit32.band(E, F), bit32.band(bit32.bnot(E), G))
			local Temp1 = H + S1 + Ch + buffer.readu32(Constants, BufferIndex) + buffer.readu32(Offsets, BufferIndex)
			H, G, F, E, D = G, F, E, D + Temp1, C

			local S0 = bit32.bxor(bit32.rrotate(A, 2), bit32.rrotate(A, 13), bit32.rrotate(A, 22))
			local Maj = bit32.bxor(bit32.band(A, B), bit32.band(A, C), bit32.band(B, C))
			C, B, A = B, A, Temp1 + S0 + Maj
		end

		A, B, C, D, E, F, G, H =
			bit32.bor(A + OldA, 0),
			bit32.bor(B + OldB, 0),
			bit32.bor(C + OldC, 0),
			bit32.bor(D + OldD, 0),
			bit32.bor(E + OldE, 0),
			bit32.bor(F + OldF, 0),
			bit32.bor(G + OldG, 0),
			bit32.bor(H + OldH, 0)
	end

	return A, B, C, D, E, F, G
end

local function SHA224(Message: buffer, Salt: buffer?): (string, buffer)
	if Salt and buffer.len(Salt) > 0 then
		local MessageWithSalt = buffer.create(buffer.len(Message) + buffer.len(Salt))

		buffer.copy(MessageWithSalt, 0, Message)
		buffer.copy(MessageWithSalt, buffer.len(Message), Salt)

		Message = MessageWithSalt
	end

	local ProcessedMessage, Length = PreProcess(Message)
	local A, B, C, D, E, F, G = DigestBlocks(ProcessedMessage, Length)

	local Digest = buffer.create(28)

	buffer.writeu32(Digest, 0, A)
	buffer.writeu32(Digest, 4, B)
	buffer.writeu32(Digest, 8, C)
	buffer.writeu32(Digest, 12, D)
	buffer.writeu32(Digest, 16, E)
	buffer.writeu32(Digest, 20, F)
	buffer.writeu32(Digest, 24, G)

	return string.format(FORMAT_STRING, A, B, C, D, E, F, G), Digest
end

local FORMAT_STRING = string.rep("%08x", 8)

local CONSTANTS = buffer.create(256) do -- CONSTANTS = k
	local RoundConstants = {
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
		0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
		0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
		0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
		0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
		0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
		0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
	}

	for Index, Constant in ipairs(RoundConstants) do
		local BufferOffset = (Index - 1) * 4
		buffer.writeu32(CONSTANTS, BufferOffset, Constant)
	end
end

local function PreProcess(Contents: buffer): (buffer, number)
	local ContentLength = buffer.len(Contents)
	local Padding = -(ContentLength + 9) % 64

	local NewContentLength = ContentLength + 1 + Padding + 8
	local NewContent = buffer.create(NewContentLength)
	buffer.copy(NewContent, 0, Contents)
	buffer.writeu8(NewContent, ContentLength, 128)
	local Length8 = ContentLength * 8
	for Index = 7, 0, -1 do
		local Remainder = Length8 % 256
		buffer.writeu8(NewContent, Index + ContentLength + 1 + Padding, Remainder)
		Length8 = (Length8 - Remainder) / 256
	end

	return NewContent, NewContentLength
end

local OFFSETS = buffer.create(256)
local function DigestBlocks(Blocks: buffer, Length: number): (number, number, number, number, number, number, number, number)
	local A, B, C, D = 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
	local E, F, G, H = 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19

	local Offsets = OFFSETS
	local Constants = CONSTANTS

	for Offset = 0, Length - 1, 64 do
		for BlockIndex = 0, 60, 4 do
			buffer.writeu32(Offsets, BlockIndex, bit32.byteswap(buffer.readu32(Blocks, Offset + BlockIndex)))
		end

		for Index = 64, 252, 4 do
			local Sub15 = buffer.readu32(Offsets, Index - 60)
			local S0 = bit32.bxor(bit32.rrotate(Sub15, 7), bit32.rrotate(Sub15, 18), bit32.rshift(Sub15, 3))

			local Sub2 = buffer.readu32(Offsets, Index - 8)
			local S1 = bit32.bxor(bit32.rrotate(Sub2, 17), bit32.rrotate(Sub2, 19), bit32.rshift(Sub2, 10))

			local Sub7, Sub16 = buffer.readu32(Offsets, Index - 28), buffer.readu32(Offsets, Index - 64)
			buffer.writeu32(Offsets, Index, (Sub16 + S0 + Sub7 + S1))
		end

		local OldA, OldB, OldC, OldD, OldE, OldF, OldG, OldH = A, B, C, D, E, F, G, H

		for BufferIndex = 0, 252, 4 do
			local S1 = bit32.bxor(bit32.rrotate(E, 6), bit32.rrotate(E, 11), bit32.rrotate(E, 25))
			local Ch = bit32.bxor(bit32.band(E, F), bit32.band(bit32.bnot(E), G))
			local Temp1 = H + S1 + Ch + buffer.readu32(Constants, BufferIndex) + buffer.readu32(Offsets, BufferIndex)
			H, G, F, E, D = G, F, E, D + Temp1, C

			local S0 = bit32.bxor(bit32.rrotate(A, 2), bit32.rrotate(A, 13), bit32.rrotate(A, 22))
			local Maj = bit32.bxor(bit32.band(A, B), bit32.band(A, C), bit32.band(B, C))
			C, B, A = B, A, Temp1 + S0 + Maj
		end

		A, B, C, D, E, F, G, H =
			bit32.bor(A + OldA, 0),
			bit32.bor(B + OldB, 0),
			bit32.bor(C + OldC, 0),
			bit32.bor(D + OldD, 0),
			bit32.bor(E + OldE, 0),
			bit32.bor(F + OldF, 0),
			bit32.bor(G + OldG, 0),
			bit32.bor(H + OldH, 0)
	end

	return A, B, C, D, E, F, G, H
end

local function SHA256(Message: buffer, Salt: buffer?): (string, buffer)
	if Salt and buffer.len(Salt) > 0 then
		local MessageWithSalt = buffer.create(buffer.len(Message) + buffer.len(Salt))

		buffer.copy(MessageWithSalt, 0, Message)
		buffer.copy(MessageWithSalt, buffer.len(Message), Salt)

		Message = MessageWithSalt
	end

	local ProcessedMessage, Length = PreProcess(Message)
	local A, B, C, D, E, F, G, H = DigestBlocks(ProcessedMessage, Length)

	local Digest = buffer.create(32)

	buffer.writeu32(Digest, 0, A)
	buffer.writeu32(Digest, 4, B)
	buffer.writeu32(Digest, 8, C)
	buffer.writeu32(Digest, 12, D)
	buffer.writeu32(Digest, 16, E)
	buffer.writeu32(Digest, 20, F)
	buffer.writeu32(Digest, 24, G)
	buffer.writeu32(Digest, 28, H)

	return string.format(FORMAT_STRING, A, B, C, D, E, F, G, H), Digest
end

local FRONT_VALUES = buffer.create(32)
local BACK_VALUES = buffer.create(32)
local WORKING_DIGEST = buffer.create(48)

local FRONTK: {number}, BACKK: {number} do
	FRONTK = {
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 
		0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 
		0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 
		0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 
		0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 
		0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 
		0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 
		0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 
		0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 
		0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 
		0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 
		0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2, 0xca273ece, 
		0xd186b8c7, 0xeada7dd6, 0xf57d4f7f, 0x06f067aa, 0x0a637dc5, 
		0x113f9804, 0x1b710b35, 0x28db77f5, 0x32caab7b, 0x3c9ebe0a, 
		0x431d67c4, 0x4cc5d4be, 0x597f299c, 0x5fcb6fab, 0x6c44198c,
	}

	BACKK = {
		0xd728ae22, 0x23ef65cd, 0xec4d3b2f, 0x8189dbbc, 0xf348b538,
		0xb605d019, 0xaf194f9b, 0xda6d8118, 0xa3030242, 0x45706fbe,
		0x4ee4b28c, 0xd5ffb4e2, 0xf27b896f, 0x3b1696b1, 0x25c71235,
		0xcf692694, 0x9ef14ad2, 0x384f25e3, 0x8b8cd5b5, 0x77ac9c65,
		0x592b0275, 0x6ea6e483, 0xbd41fbd4, 0x831153b5, 0xee66dfab,
		0x2db43210, 0x98fb213f, 0xbeef0ee4, 0x3da88fc2, 0x930aa725,
		0xe003826f, 0x0a0e6e70, 0x46d22ffc, 0x5c26c926, 0x5ac42aed,
		0x9d95b3df, 0x8baf63de, 0x3c77b2a8, 0x47edaee6, 0x1482353b,
		0x4cf10364, 0xbc423001, 0xd0f89791, 0x0654be30, 0xd6ef5218,
		0x5565a910, 0x5771202a, 0x32bbd1b8, 0xb8d2d0c8, 0x5141ab53,
		0xdf8eeb99, 0xe19b48a8, 0xc5c95a63, 0xe3418acb, 0x7763e373,
		0xd6b2b8a3, 0x5defb2fc, 0x43172f60, 0xa1f0ab72, 0x1a6439ec,
		0x23631e28, 0xde82bde9, 0xb2c67915, 0xe372532b, 0xea26619c,
		0x21c0c207, 0xcde0eb1e, 0xee6ed178, 0x72176fba, 0xa2c898a6,
		0xbef90dae, 0x131c471b, 0x23047d84, 0x40c72493, 0x15c9bebc,
		0x9c100d4c, 0xcb3e42b6, 0xfc657e2a, 0x3ad6faec, 0x4a475817,
	}
end

do
	local INITIAL_FRONT = {0xcbbb9d5d, 0x629a292a, 0x9159015a, 0x152fecd8, 0x67332667, 0x8eb44a87, 0xdb0c2e0d, 0x47b5481d}
	local INITIAL_BACK = {0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4}

	for Index = 1, 8 do
		local Offset = (Index - 1) * 4
		buffer.writeu32(FRONT_VALUES, Offset, INITIAL_FRONT[Index])
		buffer.writeu32(BACK_VALUES, Offset, INITIAL_BACK[Index])
	end
end

local BLOCK_FRONT = table.create(80)
local BLOCK_BACK = table.create(80)

local FORMAT_STRING = string.rep("%08x", 12)

local function PreProcess(Contents: buffer): (buffer, number)
	local ContentLength = buffer.len(Contents)
	local Padding = (128 - ((ContentLength + 17) % 128)) % 128
	local NewContentLength = ContentLength + 1 + Padding + 16

	local NewContent = buffer.create(NewContentLength)
	buffer.copy(NewContent, 0, Contents)
	buffer.writeu8(NewContent, ContentLength, 0x80)

	buffer.fill(NewContent, ContentLength + 1, 0, Padding + 8)

	local Length8 = ContentLength * 8
	local LengthOffset = ContentLength + 1 + Padding + 8

	for Index = 7, 0, -1 do
		buffer.writeu8(NewContent, LengthOffset + Index, Length8 % 256)
		Length8 = Length8 // 256
	end

	return NewContent, NewContentLength
end

local function DigestBlock(Blocks: buffer, Length: number, Digest: buffer)
	local BlockFront, BlockBack = BLOCK_FRONT, BLOCK_BACK
	local FrontK, BackK = FRONTK, BACKK

	local BAND, BOR, XOR = bit32.band, bit32.bor, bit32.bxor
	local ShiftLeft, RightShift = bit32.lshift, bit32.rshift
	local Swap = bit32.byteswap

	local H1F, H2F, H3F, H4F = buffer.readu32(FRONT_VALUES, 0), buffer.readu32(FRONT_VALUES, 4), buffer.readu32(FRONT_VALUES, 8), buffer.readu32(FRONT_VALUES, 12)
	local H5F, H6F, H7F, H8F = buffer.readu32(FRONT_VALUES, 16), buffer.readu32(FRONT_VALUES, 20), buffer.readu32(FRONT_VALUES, 24), buffer.readu32(FRONT_VALUES, 28)
	local H1B, H2B, H3B, H4B = buffer.readu32(BACK_VALUES, 0), buffer.readu32(BACK_VALUES, 4), buffer.readu32(BACK_VALUES, 8), buffer.readu32(BACK_VALUES, 12)
	local H5B, H6B, H7B, H8B = buffer.readu32(BACK_VALUES, 16), buffer.readu32(BACK_VALUES, 20), buffer.readu32(BACK_VALUES, 24), buffer.readu32(BACK_VALUES, 28)

	for Offset = 0, Length - 1, 128 do
		for T = 1, 16 do
			local ByteOffset = Offset + (T - 1) * 8
			BlockFront[T] = Swap(buffer.readu32(Blocks, ByteOffset))
			BlockBack[T] = Swap(buffer.readu32(Blocks, ByteOffset + 4))
		end

		for T = 17, 80 do
			local FT15, BT15 = BlockFront[T - 15], BlockBack[T - 15]

			local S0Front = XOR(RightShift(FT15, 1), ShiftLeft(BT15, 31), RightShift(FT15, 8), ShiftLeft(BT15, 24), RightShift(FT15, 7))
			local S0Back = XOR(RightShift(BT15, 1), ShiftLeft(FT15, 31), RightShift(BT15, 8), ShiftLeft(FT15, 24), RightShift(BT15, 7), ShiftLeft(FT15, 25))

			local FT2, BT2 = BlockFront[T - 2], BlockBack[T - 2]

			local S1Front = XOR(RightShift(FT2, 19), ShiftLeft(BT2, 13), ShiftLeft(FT2, 3), RightShift(BT2, 29), RightShift(FT2, 6))
			local S1Back = XOR(RightShift(BT2, 19), ShiftLeft(FT2, 13), ShiftLeft(BT2, 3), RightShift(FT2, 29), RightShift(BT2, 6), ShiftLeft(FT2, 26))

			local TempBack = BlockBack[T - 16] + S0Back + BlockBack[T - 7] + S1Back
			BlockBack[T] = BOR(TempBack, 0)
			BlockFront[T] = BlockFront[T - 16] + S0Front + BlockFront[T - 7] + S1Front + TempBack // 0x100000000
		end

		local AF, AB = H1F, H1B
		local BF, BB = H2F, H2B
		local CF, CB = H3F, H3B
		local DF, DB = H4F, H4B
		local EF, EB = H5F, H5B
		local FF, FB = H6F, H6B
		local GF, GB = H7F, H7B
		local HF, HB = H8F, H8B

		for T = 1, 80 do
			local S1Front = XOR(RightShift(EF, 14), ShiftLeft(EB, 18), RightShift(EF, 18), ShiftLeft(EB, 14), ShiftLeft(EF, 23), RightShift(EB, 9))
			local S1Back = XOR(RightShift(EB, 14), ShiftLeft(EF, 18), RightShift(EB, 18), ShiftLeft(EF, 14), ShiftLeft(EB, 23), RightShift(EF, 9))

			local S0Front = XOR(RightShift(AF, 28), ShiftLeft(AB, 4), ShiftLeft(AF, 30), RightShift(AB, 2), ShiftLeft(AF, 25), RightShift(AB, 7))
			local S0Back = XOR(RightShift(AB, 28), ShiftLeft(AF, 4), ShiftLeft(AB, 30), RightShift(AF, 2), ShiftLeft(AB, 25), RightShift(AF, 7))

			local ChFront = BOR(BAND(EF, FF), BAND(XOR(EF, 0xFFFFFFFF), GF))
			local ChBack = BOR(BAND(EB, FB), BAND(XOR(EB, 0xFFFFFFFF), GB))

			local MajFront = BAND(CF, BF) + BAND(AF, XOR(CF, BF))
			local MajBack = BAND(CB, BB) + BAND(AB, XOR(CB, BB))

			local Temp1Back = HB + S1Back + ChBack + BackK[T] + BlockBack[T]
			local Temp1Front = HF + S1Front + ChFront + FrontK[T] + BlockFront[T] + Temp1Back // 0x100000000
			Temp1Back = BOR(Temp1Back, 0)

			local Temp2Back = S0Back + MajBack
			local Temp2Front = S0Front + MajFront

			HF, HB = GF, GB
			GF, GB = FF, FB
			FF, FB = EF, EB

			EB = DB + Temp1Back
			EF = DF + Temp1Front + EB // 0x100000000
			EB = BOR(EB, 0)

			DF, DB = CF, CB
			CF, CB = BF, BB
			BF, BB = AF, AB

			AB = Temp1Back + Temp2Back
			AF = Temp1Front + Temp2Front + AB // 0x100000000
			AB = BOR(AB, 0)
		end

		H1B = H1B + AB
		H1F = BOR(H1F + AF + H1B // 0x100000000, 0)
		H1B = BOR(H1B, 0)

		H2B = H2B + BB
		H2F = BOR(H2F + BF + H2B // 0x100000000, 0)
		H2B = BOR(H2B, 0)

		H3B = H3B + CB
		H3F = BOR(H3F + CF + H3B // 0x100000000, 0)
		H3B = BOR(H3B, 0)

		H4B = H4B + DB
		H4F = BOR(H4F + DF + H4B // 0x100000000, 0)
		H4B = BOR(H4B, 0)

		H5B = H5B + EB
		H5F = BOR(H5F + EF + H5B // 0x100000000, 0)
		H5B = BOR(H5B, 0)

		H6B = H6B + FB
		H6F = BOR(H6F + FF + H6B // 0x100000000, 0)
		H6B = BOR(H6B, 0)

		H7B = H7B + GB
		H7F = BOR(H7F + GF + H7B // 0x100000000, 0)
		H7B = BOR(H7B, 0)

		H8B = H8B + HB
		H8F = BOR(H8F + HF + H8B // 0x100000000, 0)
		H8B = BOR(H8B, 0)
	end

	buffer.writeu32(Digest, 0, H1F)
	buffer.writeu32(Digest, 4, H1B)
	buffer.writeu32(Digest, 8, H2F)
	buffer.writeu32(Digest, 12, H2B)
	buffer.writeu32(Digest, 16, H3F)
	buffer.writeu32(Digest, 20, H3B)
	buffer.writeu32(Digest, 24, H4F)
	buffer.writeu32(Digest, 28, H4B)
	buffer.writeu32(Digest, 32, H5F)
	buffer.writeu32(Digest, 36, H5B)
	buffer.writeu32(Digest, 40, H6F)
	buffer.writeu32(Digest, 44, H6B)
end

local function SHA384(Message: buffer, Salt: buffer?): (string, buffer)
	if Salt and buffer.len(Salt) > 0 then
		local MessageWithSalt = buffer.create(buffer.len(Message) + buffer.len(Salt))
		buffer.copy(MessageWithSalt, 0, Message)
		buffer.copy(MessageWithSalt, buffer.len(Message), Salt)
		Message = MessageWithSalt
	end

	local ProcessedMessage, Length = PreProcess(Message)

	DigestBlock(ProcessedMessage, Length, WORKING_DIGEST)

	local H1F, H1B = buffer.readu32(WORKING_DIGEST, 0), buffer.readu32(WORKING_DIGEST, 4)
	local H2F, H2B = buffer.readu32(WORKING_DIGEST, 8), buffer.readu32(WORKING_DIGEST, 12)
	local H3F, H3B = buffer.readu32(WORKING_DIGEST, 16), buffer.readu32(WORKING_DIGEST, 20)
	local H4F, H4B = buffer.readu32(WORKING_DIGEST, 24), buffer.readu32(WORKING_DIGEST, 28)
	local H5F, H5B = buffer.readu32(WORKING_DIGEST, 32), buffer.readu32(WORKING_DIGEST, 36)
	local H6F, H6B = buffer.readu32(WORKING_DIGEST, 40), buffer.readu32(WORKING_DIGEST, 44)

	local ReturnDigest = buffer.create(48)
	buffer.copy(ReturnDigest, 0, WORKING_DIGEST)

	return string.format(FORMAT_STRING, H1F, H1B, H2F, H2B, H3F, H3B, H4F, H4B, H5F, H5B, H6F, H6B), ReturnDigest
end

local FRONT_VALUES = buffer.create(32)
local BACK_VALUES = buffer.create(32)
local WORKING_DIGEST = buffer.create(64)

local FRONTK: {number}, BACKK: {number} do
	FRONTK = {
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 
		0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 
		0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 
		0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 
		0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 
		0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 
		0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 
		0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 
		0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 
		0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 
		0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 
		0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2, 0xca273ece, 
		0xd186b8c7, 0xeada7dd6, 0xf57d4f7f, 0x06f067aa, 0x0a637dc5, 
		0x113f9804, 0x1b710b35, 0x28db77f5, 0x32caab7b, 0x3c9ebe0a, 
		0x431d67c4, 0x4cc5d4be, 0x597f299c, 0x5fcb6fab, 0x6c44198c,
	}

	BACKK = {
		0xd728ae22, 0x23ef65cd, 0xec4d3b2f, 0x8189dbbc, 0xf348b538,
		0xb605d019, 0xaf194f9b, 0xda6d8118, 0xa3030242, 0x45706fbe,
		0x4ee4b28c, 0xd5ffb4e2, 0xf27b896f, 0x3b1696b1, 0x25c71235,
		0xcf692694, 0x9ef14ad2, 0x384f25e3, 0x8b8cd5b5, 0x77ac9c65,
		0x592b0275, 0x6ea6e483, 0xbd41fbd4, 0x831153b5, 0xee66dfab,
		0x2db43210, 0x98fb213f, 0xbeef0ee4, 0x3da88fc2, 0x930aa725,
		0xe003826f, 0x0a0e6e70, 0x46d22ffc, 0x5c26c926, 0x5ac42aed,
		0x9d95b3df, 0x8baf63de, 0x3c77b2a8, 0x47edaee6, 0x1482353b,
		0x4cf10364, 0xbc423001, 0xd0f89791, 0x0654be30, 0xd6ef5218,
		0x5565a910, 0x5771202a, 0x32bbd1b8, 0xb8d2d0c8, 0x5141ab53,
		0xdf8eeb99, 0xe19b48a8, 0xc5c95a63, 0xe3418acb, 0x7763e373,
		0xd6b2b8a3, 0x5defb2fc, 0x43172f60, 0xa1f0ab72, 0x1a6439ec,
		0x23631e28, 0xde82bde9, 0xb2c67915, 0xe372532b, 0xea26619c,
		0x21c0c207, 0xcde0eb1e, 0xee6ed178, 0x72176fba, 0xa2c898a6,
		0xbef90dae, 0x131c471b, 0x23047d84, 0x40c72493, 0x15c9bebc,
		0x9c100d4c, 0xcb3e42b6, 0xfc657e2a, 0x3ad6faec, 0x4a475817,
	}
end

do
	local INITIAL_FRONT = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19}
	local INITIAL_BACK = {0xf3bcc908, 0x84caa73b, 0xfe94f82b, 0x5f1d36f1, 0xade682d1, 0x2b3e6c1f, 0xfb41bd6b, 0x137e2179}

	for Index = 1, 8 do
		local Offset = (Index - 1) * 4
		buffer.writeu32(FRONT_VALUES, Offset, INITIAL_FRONT[Index])
		buffer.writeu32(BACK_VALUES, Offset, INITIAL_BACK[Index])
	end
end

local BLOCK_FRONT = table.create(80)
local BLOCK_BACK = table.create(80)

local FORMAT_STRING = string.rep("%08x", 16)

local function PreProcess(Contents: buffer): (buffer, number)
	local ContentLength = buffer.len(Contents)
	local Padding = (128 - ((ContentLength + 17) % 128)) % 128
	local NewContentLength = ContentLength + 1 + Padding + 16

	local NewContent = buffer.create(NewContentLength)
	buffer.copy(NewContent, 0, Contents)
	buffer.writeu8(NewContent, ContentLength, 0x80)

	buffer.fill(NewContent, ContentLength + 1, 0, Padding + 8)

	local Length8 = ContentLength * 8
	local LengthOffset = ContentLength + 1 + Padding + 8

	for Index = 7, 0, -1 do
		buffer.writeu8(NewContent, LengthOffset + Index, Length8 % 256)
		Length8 = Length8 // 256
	end

	return NewContent, NewContentLength
end

local function DigestBlock(Blocks: buffer, Length: number, Digest: buffer)
	local BlockFront, BlockBack = BLOCK_FRONT, BLOCK_BACK
	local FrontK, BackK = FRONTK, BACKK

	local BAND, BOR, XOR = bit32.band, bit32.bor, bit32.bxor
	local ShiftLeft, RightShift = bit32.lshift, bit32.rshift
	local Swap = bit32.byteswap

	local H1F, H2F, H3F, H4F = buffer.readu32(FRONT_VALUES, 0), buffer.readu32(FRONT_VALUES, 4), buffer.readu32(FRONT_VALUES, 8), buffer.readu32(FRONT_VALUES, 12)
	local H5F, H6F, H7F, H8F = buffer.readu32(FRONT_VALUES, 16), buffer.readu32(FRONT_VALUES, 20), buffer.readu32(FRONT_VALUES, 24), buffer.readu32(FRONT_VALUES, 28)
	local H1B, H2B, H3B, H4B = buffer.readu32(BACK_VALUES, 0), buffer.readu32(BACK_VALUES, 4), buffer.readu32(BACK_VALUES, 8), buffer.readu32(BACK_VALUES, 12)
	local H5B, H6B, H7B, H8B = buffer.readu32(BACK_VALUES, 16), buffer.readu32(BACK_VALUES, 20), buffer.readu32(BACK_VALUES, 24), buffer.readu32(BACK_VALUES, 28)

	for Offset = 0, Length - 1, 128 do
		for T = 1, 16 do
			local ByteOffset = Offset + (T - 1) * 8
			BlockFront[T] = Swap(buffer.readu32(Blocks, ByteOffset))
			BlockBack[T] = Swap(buffer.readu32(Blocks, ByteOffset + 4))
		end

		for T = 17, 80 do
			local FT15, BT15 = BlockFront[T - 15], BlockBack[T - 15]

			local S0Front = XOR(RightShift(FT15, 1), ShiftLeft(BT15, 31), RightShift(FT15, 8), ShiftLeft(BT15, 24), RightShift(FT15, 7))
			local S0Back = XOR(RightShift(BT15, 1), ShiftLeft(FT15, 31), RightShift(BT15, 8), ShiftLeft(FT15, 24), RightShift(BT15, 7), ShiftLeft(FT15, 25))

			local FT2, BT2 = BlockFront[T - 2], BlockBack[T - 2]

			local S1Front = XOR(RightShift(FT2, 19), ShiftLeft(BT2, 13), ShiftLeft(FT2, 3), RightShift(BT2, 29), RightShift(FT2, 6))
			local S1Back = XOR(RightShift(BT2, 19), ShiftLeft(FT2, 13), ShiftLeft(BT2, 3), RightShift(FT2, 29), RightShift(BT2, 6), ShiftLeft(FT2, 26))

			local TempBack = BlockBack[T - 16] + S0Back + BlockBack[T - 7] + S1Back
			BlockBack[T] = BOR(TempBack, 0)
			BlockFront[T] = BlockFront[T - 16] + S0Front + BlockFront[T - 7] + S1Front + TempBack // 0x100000000
		end

		local AF, AB = H1F, H1B
		local BF, BB = H2F, H2B
		local CF, CB = H3F, H3B
		local DF, DB = H4F, H4B
		local EF, EB = H5F, H5B
		local FF, FB = H6F, H6B
		local GF, GB = H7F, H7B
		local HF, HB = H8F, H8B

		for T = 1, 80 do
			local S1Front = XOR(RightShift(EF, 14), ShiftLeft(EB, 18), RightShift(EF, 18), ShiftLeft(EB, 14), ShiftLeft(EF, 23), RightShift(EB, 9))
			local S1Back = XOR(RightShift(EB, 14), ShiftLeft(EF, 18), RightShift(EB, 18), ShiftLeft(EF, 14), ShiftLeft(EB, 23), RightShift(EF, 9))

			local S0Front = XOR(RightShift(AF, 28), ShiftLeft(AB, 4), ShiftLeft(AF, 30), RightShift(AB, 2), ShiftLeft(AF, 25), RightShift(AB, 7))
			local S0Back = XOR(RightShift(AB, 28), ShiftLeft(AF, 4), ShiftLeft(AB, 30), RightShift(AF, 2), ShiftLeft(AB, 25), RightShift(AF, 7))

			local ChFront = BOR(BAND(EF, FF), BAND(XOR(EF, 0xFFFFFFFF), GF))
			local ChBack = BOR(BAND(EB, FB), BAND(XOR(EB, 0xFFFFFFFF), GB))

			local MajFront = BAND(CF, BF) + BAND(AF, XOR(CF, BF))
			local MajBack = BAND(CB, BB) + BAND(AB, XOR(CB, BB))

			local Temp1Back = HB + S1Back + ChBack + BackK[T] + BlockBack[T]
			local Temp1Front = HF + S1Front + ChFront + FrontK[T] + BlockFront[T] + Temp1Back // 0x100000000
			Temp1Back = BOR(Temp1Back, 0)

			local Temp2Back = S0Back + MajBack
			local Temp2Front = S0Front + MajFront

			HF, HB = GF, GB
			GF, GB = FF, FB
			FF, FB = EF, EB

			EB = DB + Temp1Back
			EF = DF + Temp1Front + EB // 0x100000000
			EB = BOR(EB, 0)

			DF, DB = CF, CB
			CF, CB = BF, BB
			BF, BB = AF, AB

			AB = Temp1Back + Temp2Back
			AF = Temp1Front + Temp2Front + AB // 0x100000000
			AB = BOR(AB, 0)
		end

		H1B = H1B + AB
		H1F = BOR(H1F + AF + H1B // 0x100000000, 0)
		H1B = BOR(H1B, 0)

		H2B = H2B + BB
		H2F = BOR(H2F + BF + H2B // 0x100000000, 0)
		H2B = BOR(H2B, 0)

		H3B = H3B + CB
		H3F = BOR(H3F + CF + H3B // 0x100000000, 0)
		H3B = BOR(H3B, 0)

		H4B = H4B + DB
		H4F = BOR(H4F + DF + H4B // 0x100000000, 0)
		H4B = BOR(H4B, 0)

		H5B = H5B + EB
		H5F = BOR(H5F + EF + H5B // 0x100000000, 0)
		H5B = BOR(H5B, 0)

		H6B = H6B + FB
		H6F = BOR(H6F + FF + H6B // 0x100000000, 0)
		H6B = BOR(H6B, 0)

		H7B = H7B + GB
		H7F = BOR(H7F + GF + H7B // 0x100000000, 0)
		H7B = BOR(H7B, 0)

		H8B = H8B + HB
		H8F = BOR(H8F + HF + H8B // 0x100000000, 0)
		H8B = BOR(H8B, 0)
	end

	buffer.writeu32(Digest, 0, H1F)
	buffer.writeu32(Digest, 4, H1B)
	buffer.writeu32(Digest, 8, H2F)
	buffer.writeu32(Digest, 12, H2B)
	buffer.writeu32(Digest, 16, H3F)
	buffer.writeu32(Digest, 20, H3B)
	buffer.writeu32(Digest, 24, H4F)
	buffer.writeu32(Digest, 28, H4B)
	buffer.writeu32(Digest, 32, H5F)
	buffer.writeu32(Digest, 36, H5B)
	buffer.writeu32(Digest, 40, H6F)
	buffer.writeu32(Digest, 44, H6B)
	buffer.writeu32(Digest, 48, H7F)
	buffer.writeu32(Digest, 52, H7B)
	buffer.writeu32(Digest, 56, H8F)
	buffer.writeu32(Digest, 60, H8B)
end

local function SHA512(Message: buffer, Salt: buffer?): (string, buffer)
	if Salt and buffer.len(Salt) > 0 then
		local MessageWithSalt = buffer.create(buffer.len(Message) + buffer.len(Salt))
		buffer.copy(MessageWithSalt, 0, Message)
		buffer.copy(MessageWithSalt, buffer.len(Message), Salt)
		Message = MessageWithSalt
	end

	local ProcessedMessage, Length = PreProcess(Message)

	DigestBlock(ProcessedMessage, Length, WORKING_DIGEST)

	local H1F, H1B = buffer.readu32(WORKING_DIGEST, 0), buffer.readu32(WORKING_DIGEST, 4)
	local H2F, H2B = buffer.readu32(WORKING_DIGEST, 8), buffer.readu32(WORKING_DIGEST, 12)
	local H3F, H3B = buffer.readu32(WORKING_DIGEST, 16), buffer.readu32(WORKING_DIGEST, 20)
	local H4F, H4B = buffer.readu32(WORKING_DIGEST, 24), buffer.readu32(WORKING_DIGEST, 28)
	local H5F, H5B = buffer.readu32(WORKING_DIGEST, 32), buffer.readu32(WORKING_DIGEST, 36)
	local H6F, H6B = buffer.readu32(WORKING_DIGEST, 40), buffer.readu32(WORKING_DIGEST, 44)
	local H7F, H7B = buffer.readu32(WORKING_DIGEST, 48), buffer.readu32(WORKING_DIGEST, 52)
	local H8F, H8B = buffer.readu32(WORKING_DIGEST, 56), buffer.readu32(WORKING_DIGEST, 60)

	local ReturnDigest = buffer.create(64)
	buffer.copy(ReturnDigest, 0, WORKING_DIGEST)

	return string.format(FORMAT_STRING, H1F, H1B, H2F, H2B, H3F, H3B, H4F, H4B, H5F, H5B, H6F, H6B, H7F, H7B, H8F, H8B), ReturnDigest
end

local SHA3 = {}

local ENCODE_LOOKUP = buffer.create(256 * 2) do
	local HexChars = "0123456789abcdef"
	for Byte = 0, 255 do
		local HighNibble = bit32.rshift(Byte, 4)
		local LowNibble = Byte % 16

		local HighChar = string.byte(HexChars, HighNibble + 1)
		local LowChar = string.byte(HexChars, LowNibble + 1)

		local Combined = HighChar + bit32.lshift(LowChar, 8)
		buffer.writeu16(ENCODE_LOOKUP, Byte * 2, Combined)
	end
end

local LOW_ROUND, HIGH_ROUND = buffer.create(96), buffer.create(96) do
	local HighFactorKeccak = 0
	local ShiftRegister = 29
	local function GetNextBit(): number
		local Result = ShiftRegister % 2
		ShiftRegister =  bit32.bxor((ShiftRegister - Result) // 2, 142 * Result)

		return Result
	end

	for Index = 0, 23 do
		local LowValue: number, Multiplier: number = 0, nil

		for _ = 1, 6 do
			Multiplier = if Multiplier then Multiplier * Multiplier * 2 else 1
			LowValue += GetNextBit() * Multiplier
		end

		local HighValue = GetNextBit() * Multiplier
		buffer.writeu32(HIGH_ROUND, Index * 4, HighValue)
		buffer.writeu32(LOW_ROUND, Index * 4, LowValue + HighValue * HighFactorKeccak)
	end
end

local LANES_LOW = buffer.create(100)
local LANES_HIGH = buffer.create(100)

local function Keccak(LanesLow: buffer, LanesHigh: buffer, InputBuffer: buffer, Offset: number, Size: number, BlockSizeInBytes: number): ()
	local QuadWordsQuantity = BlockSizeInBytes // 8
	local RCHigh, RCLow = HIGH_ROUND, LOW_ROUND
	local XOR = bit32.bxor

	for Position = Offset, Offset + Size - 1, BlockSizeInBytes do
		for Index = 0, (QuadWordsQuantity - 1) * 4, 4 do
			local BufferPos = Position + Index * 2

			buffer.writeu32(LanesLow, Index, XOR(
				buffer.readu32(LanesLow, Index),
				buffer.readu32(InputBuffer, BufferPos)
				))

			buffer.writeu32(LanesHigh, Index, XOR(
				buffer.readu32(LanesHigh, Index),
				buffer.readu32(InputBuffer, BufferPos + 4)
				))
		end

		local Lane01Low, Lane01High = buffer.readu32(LanesLow, 0), buffer.readu32(LanesHigh, 0)
		local Lane02Low, Lane02High = buffer.readu32(LanesLow, 4), buffer.readu32(LanesHigh, 4)
		local Lane03Low, Lane03High = buffer.readu32(LanesLow, 8), buffer.readu32(LanesHigh, 8)

		local Lane04Low, Lane04High = buffer.readu32(LanesLow, 12), buffer.readu32(LanesHigh, 12)
		local Lane05Low, Lane05High = buffer.readu32(LanesLow, 16), buffer.readu32(LanesHigh, 16)
		local Lane06Low, Lane06High = buffer.readu32(LanesLow, 20), buffer.readu32(LanesHigh, 20)

		local Lane07Low, Lane07High = buffer.readu32(LanesLow, 24), buffer.readu32(LanesHigh, 24)
		local Lane08Low, Lane08High = buffer.readu32(LanesLow, 28), buffer.readu32(LanesHigh, 28)
		local Lane09Low, Lane09High = buffer.readu32(LanesLow, 32), buffer.readu32(LanesHigh, 32)

		local Lane10Low, Lane10High = buffer.readu32(LanesLow, 36), buffer.readu32(LanesHigh, 36)
		local Lane11Low, Lane11High = buffer.readu32(LanesLow, 40), buffer.readu32(LanesHigh, 40)
		local Lane12Low, Lane12High = buffer.readu32(LanesLow, 44), buffer.readu32(LanesHigh, 44)

		local Lane13Low, Lane13High = buffer.readu32(LanesLow, 48), buffer.readu32(LanesHigh, 48)
		local Lane14Low, Lane14High = buffer.readu32(LanesLow, 52), buffer.readu32(LanesHigh, 52)
		local Lane15Low, Lane15High = buffer.readu32(LanesLow, 56), buffer.readu32(LanesHigh, 56)

		local Lane16Low, Lane16High = buffer.readu32(LanesLow, 60), buffer.readu32(LanesHigh, 60)
		local Lane17Low, Lane17High = buffer.readu32(LanesLow, 64), buffer.readu32(LanesHigh, 64)
		local Lane18Low, Lane18High = buffer.readu32(LanesLow, 68), buffer.readu32(LanesHigh, 68)

		local Lane19Low, Lane19High = buffer.readu32(LanesLow, 72), buffer.readu32(LanesHigh, 72)
		local Lane20Low, Lane20High = buffer.readu32(LanesLow, 76), buffer.readu32(LanesHigh, 76)
		local Lane21Low, Lane21High = buffer.readu32(LanesLow, 80), buffer.readu32(LanesHigh, 80)

		local Lane22Low, Lane22High = buffer.readu32(LanesLow, 84), buffer.readu32(LanesHigh, 84)
		local Lane23Low, Lane23High = buffer.readu32(LanesLow, 88), buffer.readu32(LanesHigh, 88)
		local Lane24Low, Lane24High = buffer.readu32(LanesLow, 92), buffer.readu32(LanesHigh, 92)

		local Lane25Low, Lane25High = buffer.readu32(LanesLow, 96), buffer.readu32(LanesHigh, 96)

		for RoundIndex = 0, 92, 4 do
			local Column1Low, Column1High = XOR(Lane01Low, Lane06Low, Lane11Low, Lane16Low, Lane21Low), XOR(Lane01High, Lane06High, Lane11High, Lane16High, Lane21High)
			local Column2Low, Column2High = XOR(Lane02Low, Lane07Low, Lane12Low, Lane17Low, Lane22Low), XOR(Lane02High, Lane07High, Lane12High, Lane17High, Lane22High)
			local Column3Low, Column3High = XOR(Lane03Low, Lane08Low, Lane13Low, Lane18Low, Lane23Low), XOR(Lane03High, Lane08High, Lane13High, Lane18High, Lane23High)
			local Column4Low, Column4High = XOR(Lane04Low, Lane09Low, Lane14Low, Lane19Low, Lane24Low), XOR(Lane04High, Lane09High, Lane14High, Lane19High, Lane24High)
			local Column5Low, Column5High = XOR(Lane05Low, Lane10Low, Lane15Low, Lane20Low, Lane25Low), XOR(Lane05High, Lane10High, Lane15High, Lane20High, Lane25High)

			local DeltaLow, DeltaHigh = XOR(Column1Low, Column3Low * 2 + Column3High // 2147483648), XOR(Column1High, Column3High * 2 + Column3Low // 2147483648)
			local Temp0Low, Temp0High = XOR(DeltaLow, Lane02Low), XOR(DeltaHigh, Lane02High)
			local Temp1Low, Temp1High = XOR(DeltaLow, Lane07Low), XOR(DeltaHigh, Lane07High)
			local Temp2Low, Temp2High = XOR(DeltaLow, Lane12Low), XOR(DeltaHigh, Lane12High)
			local Temp3Low, Temp3High = XOR(DeltaLow, Lane17Low), XOR(DeltaHigh, Lane17High)
			local Temp4Low, Temp4High = XOR(DeltaLow, Lane22Low), XOR(DeltaHigh, Lane22High)

			Lane02Low = Temp1Low // 1048576 + (Temp1High * 4096); Lane02High = Temp1High // 1048576 + (Temp1Low * 4096)
			Lane07Low = Temp3Low // 524288 + (Temp3High * 8192); Lane07High = Temp3High // 524288 + (Temp3Low * 8192)
			Lane12Low = Temp0Low * 2 + Temp0High // 2147483648; Lane12High = Temp0High * 2 + Temp0Low // 2147483648
			Lane17Low = Temp2Low * 1024 + Temp2High // 4194304; Lane17High = Temp2High * 1024 + Temp2Low // 4194304
			Lane22Low = Temp4Low * 4 + Temp4High // 1073741824; Lane22High = Temp4High * 4 + Temp4Low // 1073741824

			DeltaLow = XOR(Column2Low, Column4Low * 2 + Column4High // 2147483648); DeltaHigh = XOR(Column2High, Column4High * 2 + Column4Low // 2147483648)
			Temp0Low = XOR(DeltaLow, Lane03Low); Temp0High = XOR(DeltaHigh, Lane03High)
			Temp1Low = XOR(DeltaLow, Lane08Low); Temp1High = XOR(DeltaHigh, Lane08High)
			Temp2Low = XOR(DeltaLow, Lane13Low); Temp2High = XOR(DeltaHigh, Lane13High)
			Temp3Low = XOR(DeltaLow, Lane18Low); Temp3High = XOR(DeltaHigh, Lane18High)
			Temp4Low = XOR(DeltaLow, Lane23Low); Temp4High = XOR(DeltaHigh, Lane23High)

			Lane03Low = Temp2Low // 2097152 + (Temp2High * 2048); Lane03High = Temp2High // 2097152 + (Temp2Low * 2048)
			Lane08Low = Temp4Low // 8 + bit32.bor(Temp4High * 536870912, 0); Lane08High = Temp4High // 8 + bit32.bor(Temp4Low * 536870912, 0)
			Lane13Low = Temp1Low * 64 + Temp1High // 67108864; Lane13High = Temp1High * 64 + Temp1Low // 67108864
			Lane18Low = (Temp3Low * 32768) + Temp3High // 131072; Lane18High = (Temp3High * 32768) + Temp3Low // 131072
			Lane23Low = Temp0Low // 4 + bit32.bor(Temp0High * 1073741824, 0); Lane23High = Temp0High // 4 + bit32.bor(Temp0Low * 1073741824, 0)

			DeltaLow = XOR(Column3Low, Column5Low * 2 + Column5High // 2147483648); DeltaHigh = XOR(Column3High, Column5High * 2 + Column5Low // 2147483648)
			Temp0Low = XOR(DeltaLow, Lane04Low); Temp0High = XOR(DeltaHigh, Lane04High)
			Temp1Low = XOR(DeltaLow, Lane09Low); Temp1High = XOR(DeltaHigh, Lane09High)
			Temp2Low = XOR(DeltaLow, Lane14Low); Temp2High = XOR(DeltaHigh, Lane14High)
			Temp3Low = XOR(DeltaLow, Lane19Low); Temp3High = XOR(DeltaHigh, Lane19High)
			Temp4Low = XOR(DeltaLow, Lane24Low); Temp4High = XOR(DeltaHigh, Lane24High)

			Lane04Low = bit32.bor(Temp3Low * 2097152, 0) + Temp3High // 2048; Lane04High = bit32.bor(Temp3High * 2097152, 0) + Temp3Low // 2048
			Lane09Low = bit32.bor(Temp0Low * 268435456, 0) + Temp0High // 16; Lane09High = bit32.bor(Temp0High * 268435456, 0) + Temp0Low // 16
			Lane14Low = bit32.bor(Temp2Low * 33554432, 0) + Temp2High // 128; Lane14High = bit32.bor(Temp2High * 33554432, 0) + Temp2Low // 128
			Lane19Low = Temp4Low // 256 + bit32.bor(Temp4High * 16777216, 0); Lane19High = Temp4High // 256 + bit32.bor(Temp4Low * 16777216, 0)
			Lane24Low = Temp1Low // 512 + bit32.bor(Temp1High * 8388608, 0); Lane24High = Temp1High // 512 + bit32.bor(Temp1Low * 8388608, 0)
			DeltaLow = XOR(Column4Low, Column1Low * 2 + Column1High // 2147483648); DeltaHigh = XOR(Column4High, Column1High * 2 + Column1Low // 2147483648)

			Temp0Low = XOR(DeltaLow, Lane05Low); Temp0High = XOR(DeltaHigh, Lane05High)
			Temp1Low = XOR(DeltaLow, Lane10Low); Temp1High = XOR(DeltaHigh, Lane10High)
			Temp2Low = XOR(DeltaLow, Lane15Low); Temp2High = XOR(DeltaHigh, Lane15High)
			Temp3Low = XOR(DeltaLow, Lane20Low); Temp3High = XOR(DeltaHigh, Lane20High)
			Temp4Low = XOR(DeltaLow, Lane25Low); Temp4High = XOR(DeltaHigh, Lane25High)

			Lane05Low = (Temp4Low * 16384) + Temp4High // 262144; Lane05High = (Temp4High * 16384) + Temp4Low // 262144
			Lane10Low = bit32.bor(Temp1Low * 1048576, 0) + Temp1High // 4096; Lane10High = bit32.bor(Temp1High * 1048576, 0) + Temp1Low // 4096
			Lane15Low = Temp3Low * 256 + Temp3High // 16777216; Lane15High = Temp3High * 256 + Temp3Low // 16777216
			Lane20Low = bit32.bor(Temp0Low * 134217728, 0) + Temp0High // 32; Lane20High = bit32.bor(Temp0High * 134217728, 0) + Temp0Low // 32
			Lane25Low = Temp2Low // 33554432 + Temp2High * 128; Lane25High = Temp2High // 33554432 + Temp2Low * 128

			DeltaLow = XOR(Column5Low, Column2Low * 2 + Column2High // 2147483648); DeltaHigh = XOR(Column5High, Column2High * 2 + Column2Low // 2147483648)
			Temp1Low = XOR(DeltaLow, Lane06Low); Temp1High = XOR(DeltaHigh, Lane06High)
			Temp2Low = XOR(DeltaLow, Lane11Low); Temp2High = XOR(DeltaHigh, Lane11High)
			Temp3Low = XOR(DeltaLow, Lane16Low); Temp3High = XOR(DeltaHigh, Lane16High)
			Temp4Low = XOR(DeltaLow, Lane21Low); Temp4High = XOR(DeltaHigh, Lane21High)
			Lane06Low = Temp2Low * 8 + Temp2High // 536870912; Lane06High = Temp2High * 8 + Temp2Low // 536870912
			Lane11Low = (Temp4Low * 262144) + Temp4High // 16384; Lane11High = (Temp4High * 262144) + Temp4Low // 16384
			Lane16Low = Temp1Low // 268435456 + Temp1High * 16; Lane16High = Temp1High // 268435456 + Temp1Low * 16
			Lane21Low = Temp3Low // 8388608 + Temp3High * 512; Lane21High = Temp3High // 8388608 + Temp3Low * 512
			Lane01Low = XOR(DeltaLow, Lane01Low); Lane01High = XOR(DeltaHigh, Lane01High)

			Lane01Low, Lane02Low, Lane03Low, Lane04Low, Lane05Low =  XOR(Lane01Low, bit32.band(-1 - Lane02Low, Lane03Low)),  XOR(Lane02Low, bit32.band(-1 - Lane03Low, Lane04Low)),  XOR(Lane03Low, bit32.band(-1 - Lane04Low, Lane05Low)),  XOR(Lane04Low, bit32.band(-1 - Lane05Low, Lane01Low)),  XOR(Lane05Low, bit32.band(-1 - Lane01Low, Lane02Low))
			Lane01High, Lane02High, Lane03High, Lane04High, Lane05High =  XOR(Lane01High, bit32.band(-1 - Lane02High, Lane03High)),  XOR(Lane02High, bit32.band(-1 - Lane03High, Lane04High)),  XOR(Lane03High, bit32.band(-1 - Lane04High, Lane05High)),  XOR(Lane04High, bit32.band(-1 - Lane05High, Lane01High)),  XOR(Lane05High, bit32.band(-1 - Lane01High, Lane02High))
			Lane06Low, Lane07Low, Lane08Low, Lane09Low, Lane10Low =  XOR(Lane09Low, bit32.band(-1 - Lane10Low, Lane06Low)),  XOR(Lane10Low, bit32.band(-1 - Lane06Low, Lane07Low)),  XOR(Lane06Low, bit32.band(-1 - Lane07Low, Lane08Low)),  XOR(Lane07Low, bit32.band(-1 - Lane08Low, Lane09Low)),  XOR(Lane08Low, bit32.band(-1 - Lane09Low, Lane10Low))
			Lane06High, Lane07High, Lane08High, Lane09High, Lane10High =  XOR(Lane09High, bit32.band(-1 - Lane10High, Lane06High)),  XOR(Lane10High, bit32.band(-1 - Lane06High, Lane07High)),  XOR(Lane06High, bit32.band(-1 - Lane07High, Lane08High)),  XOR(Lane07High, bit32.band(-1 - Lane08High, Lane09High)),  XOR(Lane08High, bit32.band(-1 - Lane09High, Lane10High))
			Lane11Low, Lane12Low, Lane13Low, Lane14Low, Lane15Low =  XOR(Lane12Low, bit32.band(-1 - Lane13Low, Lane14Low)),  XOR(Lane13Low, bit32.band(-1 - Lane14Low, Lane15Low)),  XOR(Lane14Low, bit32.band(-1 - Lane15Low, Lane11Low)),  XOR(Lane15Low, bit32.band(-1 - Lane11Low, Lane12Low)),  XOR(Lane11Low, bit32.band(-1 - Lane12Low, Lane13Low))
			Lane11High, Lane12High, Lane13High, Lane14High, Lane15High =  XOR(Lane12High, bit32.band(-1 - Lane13High, Lane14High)),  XOR(Lane13High, bit32.band(-1 - Lane14High, Lane15High)),  XOR(Lane14High, bit32.band(-1 - Lane15High, Lane11High)),  XOR(Lane15High, bit32.band(-1 - Lane11High, Lane12High)),  XOR(Lane11High, bit32.band(-1 - Lane12High, Lane13High))
			Lane16Low, Lane17Low, Lane18Low, Lane19Low, Lane20Low =  XOR(Lane20Low, bit32.band(-1 - Lane16Low, Lane17Low)),  XOR(Lane16Low, bit32.band(-1 - Lane17Low, Lane18Low)),  XOR(Lane17Low, bit32.band(-1 - Lane18Low, Lane19Low)),  XOR(Lane18Low, bit32.band(-1 - Lane19Low, Lane20Low)),  XOR(Lane19Low, bit32.band(-1 - Lane20Low, Lane16Low))
			Lane16High, Lane17High, Lane18High, Lane19High, Lane20High =  XOR(Lane20High, bit32.band(-1 - Lane16High, Lane17High)),  XOR(Lane16High, bit32.band(-1 - Lane17High, Lane18High)),  XOR(Lane17High, bit32.band(-1 - Lane18High, Lane19High)),  XOR(Lane18High, bit32.band(-1 - Lane19High, Lane20High)),  XOR(Lane19High, bit32.band(-1 - Lane20High, Lane16High))
			Lane21Low, Lane22Low, Lane23Low, Lane24Low, Lane25Low =  XOR(Lane23Low, bit32.band(-1 - Lane24Low, Lane25Low)),  XOR(Lane24Low, bit32.band(-1 - Lane25Low, Lane21Low)),  XOR(Lane25Low, bit32.band(-1 - Lane21Low, Lane22Low)),  XOR(Lane21Low, bit32.band(-1 - Lane22Low, Lane23Low)),  XOR(Lane22Low, bit32.band(-1 - Lane23Low, Lane24Low))
			Lane21High, Lane22High, Lane23High, Lane24High, Lane25High =  XOR(Lane23High, bit32.band(-1 - Lane24High, Lane25High)),  XOR(Lane24High, bit32.band(-1 - Lane25High, Lane21High)),  XOR(Lane25High, bit32.band(-1 - Lane21High, Lane22High)),  XOR(Lane21High, bit32.band(-1 - Lane22High, Lane23High)),  XOR(Lane22High, bit32.band(-1 - Lane23High, Lane24High))

			Lane01Low =  XOR(Lane01Low, buffer.readu32(RCLow, RoundIndex))
			Lane01High = XOR(Lane01High, buffer.readu32(RCHigh, RoundIndex))
		end

		buffer.writeu32(LanesLow, 0, Lane01Low); buffer.writeu32(LanesHigh, 0, Lane01High)
		buffer.writeu32(LanesLow, 4, Lane02Low); buffer.writeu32(LanesHigh, 4, Lane02High)
		buffer.writeu32(LanesLow, 8, Lane03Low); buffer.writeu32(LanesHigh, 8, Lane03High)
		buffer.writeu32(LanesLow, 12, Lane04Low); buffer.writeu32(LanesHigh, 12, Lane04High)
		buffer.writeu32(LanesLow, 16, Lane05Low); buffer.writeu32(LanesHigh, 16, Lane05High)
		buffer.writeu32(LanesLow, 20, Lane06Low); buffer.writeu32(LanesHigh, 20, Lane06High)
		buffer.writeu32(LanesLow, 24, Lane07Low); buffer.writeu32(LanesHigh, 24, Lane07High)
		buffer.writeu32(LanesLow, 28, Lane08Low); buffer.writeu32(LanesHigh, 28, Lane08High)
		buffer.writeu32(LanesLow, 32, Lane09Low); buffer.writeu32(LanesHigh, 32, Lane09High)
		buffer.writeu32(LanesLow, 36, Lane10Low); buffer.writeu32(LanesHigh, 36, Lane10High)
		buffer.writeu32(LanesLow, 40, Lane11Low); buffer.writeu32(LanesHigh, 40, Lane11High)
		buffer.writeu32(LanesLow, 44, Lane12Low); buffer.writeu32(LanesHigh, 44, Lane12High)
		buffer.writeu32(LanesLow, 48, Lane13Low); buffer.writeu32(LanesHigh, 48, Lane13High)
		buffer.writeu32(LanesLow, 52, Lane14Low); buffer.writeu32(LanesHigh, 52, Lane14High)
		buffer.writeu32(LanesLow, 56, Lane15Low); buffer.writeu32(LanesHigh, 56, Lane15High)
		buffer.writeu32(LanesLow, 60, Lane16Low); buffer.writeu32(LanesHigh, 60, Lane16High)
		buffer.writeu32(LanesLow, 64, Lane17Low); buffer.writeu32(LanesHigh, 64, Lane17High)
		buffer.writeu32(LanesLow, 68, Lane18Low); buffer.writeu32(LanesHigh, 68, Lane18High)
		buffer.writeu32(LanesLow, 72, Lane19Low); buffer.writeu32(LanesHigh, 72, Lane19High)
		buffer.writeu32(LanesLow, 76, Lane20Low); buffer.writeu32(LanesHigh, 76, Lane20High)
		buffer.writeu32(LanesLow, 80, Lane21Low); buffer.writeu32(LanesHigh, 80, Lane21High)
		buffer.writeu32(LanesLow, 84, Lane22Low); buffer.writeu32(LanesHigh, 84, Lane22High)
		buffer.writeu32(LanesLow, 88, Lane23Low); buffer.writeu32(LanesHigh, 88, Lane23High)
		buffer.writeu32(LanesLow, 92, Lane24Low); buffer.writeu32(LanesHigh, 92, Lane24High)
		buffer.writeu32(LanesLow, 96, Lane25Low); buffer.writeu32(LanesHigh, 96, Lane25High)
	end
end

local function ProcessSponge(Message: buffer, CapacityBits: number, OutputBytes: number, DomainSeparator: number): (string, buffer)
	local RateBytes = (1600 - CapacityBits) // 8
	buffer.fill(LANES_LOW, 0, 0, 100)
	buffer.fill(LANES_HIGH, 0, 0, 100)

	local LanesLow = LANES_LOW
	local LanesHigh  = LANES_HIGH

	local MessageLength: number = buffer.len(Message)
	local PaddedLength: number = MessageLength + 1

	local Remainder = PaddedLength % RateBytes
	if Remainder ~= 0 then
		PaddedLength += (RateBytes - Remainder)
	end

	local PaddedMessage = buffer.create(PaddedLength)

	if MessageLength > 0 then
		buffer.copy(PaddedMessage, 0, Message, 0, MessageLength)
	end

	if PaddedLength - MessageLength == 1 then
		buffer.writeu8(PaddedMessage, MessageLength, bit32.bor(DomainSeparator, 0x80))
	else
		buffer.writeu8(PaddedMessage, MessageLength, DomainSeparator)
		if PaddedLength - MessageLength > 2 then
			buffer.fill(PaddedMessage, MessageLength + 1, 0, PaddedLength - MessageLength - 2)
		end
		buffer.writeu8(PaddedMessage, PaddedLength - 1, 0x80)
	end

	Keccak(LanesLow, LanesHigh, PaddedMessage, 0, PaddedLength, RateBytes)

	local Output = buffer.create(OutputBytes)
	local Length = buffer.len(Output)
	local Hex = buffer.create(Length * 2)

	local Lookup = ENCODE_LOOKUP

	local Leftover = Length % 8
	local HexCursor = 0
	local OutputOffset = 0

	local ZeroBuffer = buffer.create(RateBytes)
	while OutputOffset < OutputBytes do
		local BytesThisRound = math.min(RateBytes, OutputBytes - OutputOffset)

		for ByteIndex = 0, BytesThisRound - 1 do
			local AbsoluteIndex = OutputOffset + ByteIndex
			if AbsoluteIndex < OutputBytes then
				local Lane = ByteIndex // 8
				local ByteInLane = ByteIndex % 8
				local LaneOffset = Lane * 4

				local Value
				if ByteInLane < 4 then
					Value = bit32.extract(buffer.readu32(LanesLow, LaneOffset), ByteInLane * 8, 8)
				else
					Value = bit32.extract(buffer.readu32(LanesHigh, LaneOffset), (ByteInLane - 4) * 8, 8)
				end
				buffer.writeu8(Output, AbsoluteIndex, Value)
			end
		end

		OutputOffset += BytesThisRound

		if OutputOffset < OutputBytes then
			Keccak(LanesLow, LanesHigh, ZeroBuffer, 0, RateBytes, RateBytes)
		end
	end

	for Index = 0, Length - Leftover - 1, 8 do
		local Hex1 = buffer.readu16(Lookup, buffer.readu8(Output, Index) * 2)
		local Hex2 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 1) * 2)
		local Hex3 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 2) * 2)
		local Hex4 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 3) * 2)
		local Hex5 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 4) * 2)
		local Hex6 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 5) * 2)
		local Hex7 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 6) * 2)
		local Hex8 = buffer.readu16(Lookup, buffer.readu8(Output, Index + 7) * 2)

		buffer.writeu16(Hex, HexCursor, Hex1)
		buffer.writeu16(Hex, HexCursor + 2, Hex2)
		buffer.writeu16(Hex, HexCursor + 4, Hex3)
		buffer.writeu16(Hex, HexCursor + 6, Hex4)
		buffer.writeu16(Hex, HexCursor + 8, Hex5)
		buffer.writeu16(Hex, HexCursor + 10, Hex6)
		buffer.writeu16(Hex, HexCursor + 12, Hex7)
		buffer.writeu16(Hex, HexCursor + 14, Hex8)

		HexCursor += 16
	end

	for Index = Length - Leftover, Length - 1 do
		local HexPair = buffer.readu16(Lookup, buffer.readu8(Output, Index) * 2)
		buffer.writeu16(Hex, HexCursor, HexPair)
		HexCursor += 2
	end
	
	return buffer.tostring(Hex), Output
end

function SHA3.SHA3_224(Message: buffer): (string, buffer)
	return ProcessSponge(Message, 448, 28, 0x06)
end

function SHA3.SHA3_256(Message: buffer): (string, buffer)
	return ProcessSponge(Message, 512, 32, 0x06)
end

function SHA3.SHA3_384(Message: buffer): (string, buffer)
	return ProcessSponge(Message, 768, 48, 0x06)
end

function SHA3.SHA3_512(Message: buffer): (string, buffer)
	return ProcessSponge(Message, 1024, 64, 0x06)
end

function SHA3.SHAKE128(Message: buffer, OutputBytes: number): (string, buffer)
	return ProcessSponge(Message, 256, OutputBytes, 0x1F)
end

function SHA3.SHAKE256(Message: buffer, OutputBytes: number): (string, buffer)
	return ProcessSponge(Message, 512, OutputBytes, 0x1F)
end

local function XXH32(Message: buffer, Seed: number?): number
	local PRIME_1, PRIME_1_HIGH, PRIME_1_LOW = 0x9e3779B1, 40503, 31153
	local PRIME_2, PRIME_2_HIGH, PRIME_2_LOW = 0x85ebca77, 34283, 51831
	local _PRIME_3, PRIME_3_HIGH, PRIME_3_LOW = 0xc2b2ae3d, 49842, 44605
	local _PRIME_4, PRIME_4_HIGH, PRIME_4_LOW = 0x27d4eb2f, 10196, 60207
	local PRIME_5, PRIME_5_HIGH, PRIME_5_LOW = 0x165667b1, 5718, 26545

	local UsedSeed = Seed or 0
	local MessageLength = buffer.len(Message)
	local Digest: number
	local CurrentOffset = 0

	if MessageLength >= 16 then
		local Accumulator1 = UsedSeed + PRIME_1 + PRIME_2
		local Accumulator2 = UsedSeed + PRIME_2
		local Accumulator3 = UsedSeed
		local Accumulator4 = UsedSeed - PRIME_1

		while CurrentOffset <= MessageLength - 16 do
			local Word1 = buffer.readu32(Message, CurrentOffset)
			local Word2 = buffer.readu32(Message, CurrentOffset + 4)
			local Word3 = buffer.readu32(Message, CurrentOffset + 8)
			local Word4 = buffer.readu32(Message, CurrentOffset + 12)

			local AHigh1, ALow1 = bit32.rshift(Word1, 16), bit32.band(Word1, 65535)
			local Mult1 = bit32.lshift((AHigh1 * PRIME_2_LOW) + (ALow1 * PRIME_2_HIGH), 16) + (ALow1 * PRIME_2_LOW)

			local Temp1 = bit32.lrotate(Accumulator1 + Mult1, 13)
			local AHigh1_2, ALow1_2 = bit32.rshift(Temp1, 16), bit32.band(Temp1, 65535)
			Accumulator1 = bit32.lshift((AHigh1_2 * PRIME_1_LOW) + (ALow1_2 * PRIME_1_HIGH), 16) + (ALow1_2 * PRIME_1_LOW)

			local AHigh2, ALow2 = bit32.rshift(Word2, 16), bit32.band(Word2, 65535)
			local Mult2 = bit32.lshift((AHigh2 * PRIME_2_LOW) + (ALow2 * PRIME_2_HIGH), 16) + (ALow2 * PRIME_2_LOW)

			local Temp2 = bit32.lrotate(Accumulator2 + Mult2, 13)
			local AHigh2_2, ALow2_2 = bit32.rshift(Temp2, 16), bit32.band(Temp2, 65535)
			Accumulator2 = bit32.lshift((AHigh2_2 * PRIME_1_LOW) + (ALow2_2 * PRIME_1_HIGH), 16) + (ALow2_2 * PRIME_1_LOW)

			local AHigh3, ALow3 = bit32.rshift(Word3, 16), bit32.band(Word3, 65535)
			local Mult3 = bit32.lshift((AHigh3 * PRIME_2_LOW) + (ALow3 * PRIME_2_HIGH), 16) + (ALow3 * PRIME_2_LOW)

			local Temp3 = bit32.lrotate(Accumulator3 + Mult3, 13)
			local AHigh3_2, ALow3_2 = bit32.rshift(Temp3, 16), bit32.band(Temp3, 65535)
			Accumulator3 = bit32.lshift((AHigh3_2 * PRIME_1_LOW) + (ALow3_2 * PRIME_1_HIGH), 16) + (ALow3_2 * PRIME_1_LOW)

			local AHigh4, ALow4 = bit32.rshift(Word4, 16), bit32.band(Word4, 65535)
			local Mult4 = bit32.lshift((AHigh4 * PRIME_2_LOW) + (ALow4 * PRIME_2_HIGH), 16) + (ALow4 * PRIME_2_LOW)

			local Temp4 = bit32.lrotate(Accumulator4 + Mult4, 13)
			local AHigh4_2, ALow4_2 = bit32.rshift(Temp4, 16), bit32.band(Temp4, 65535)
			Accumulator4 = bit32.lshift((AHigh4_2 * PRIME_1_LOW) + (ALow4_2 * PRIME_1_HIGH), 16) + (ALow4_2 * PRIME_1_LOW)

			CurrentOffset += 16
		end

		Digest = bit32.lrotate(Accumulator1, 1) + bit32.lrotate(Accumulator2, 7) + bit32.lrotate(Accumulator3, 12) + bit32.lrotate(Accumulator4, 18)
	else
		Digest = UsedSeed + PRIME_5
	end

	Digest += MessageLength

	while CurrentOffset <= MessageLength - 4 do
		if CurrentOffset + 4 <= buffer.len(Message) then
			local Word = buffer.readu32(Message, CurrentOffset)

			local AHigh_w, ALow_w = bit32.rshift(Word, 16), bit32.band(Word, 65535)
			local Mult_w = bit32.lshift((AHigh_w * PRIME_3_LOW) + (ALow_w * PRIME_3_HIGH), 16) + (ALow_w * PRIME_3_LOW)

			Digest += Mult_w

			local Rotated = bit32.lrotate(Digest, 17)
			local AHigh_r, ALow_r = bit32.rshift(Rotated, 16), bit32.band(Rotated, 65535)
			Digest = bit32.lshift((AHigh_r * PRIME_4_LOW) + (ALow_r * PRIME_4_HIGH), 16) + (ALow_r * PRIME_4_LOW)
		end
		CurrentOffset += 4
	end

	while CurrentOffset < MessageLength do
		if CurrentOffset < buffer.len(Message) then
			local ByteValue = buffer.readu8(Message, CurrentOffset)

			local AHigh_b, ALow_b = bit32.rshift(ByteValue, 16), bit32.band(ByteValue, 65535)
			local Mult_b = bit32.lshift((AHigh_b * PRIME_5_LOW) + (ALow_b * PRIME_5_HIGH), 16) + (ALow_b * PRIME_5_LOW)

			Digest += Mult_b

			local Rotated_b = bit32.lrotate(Digest, 11)
			local AHigh_rb, ALow_rb = bit32.rshift(Rotated_b, 16), bit32.band(Rotated_b, 65535)
			Digest = bit32.lshift((AHigh_rb * PRIME_1_LOW) + (ALow_rb * PRIME_1_HIGH), 16) + (ALow_rb * PRIME_1_LOW)
		end
		CurrentOffset += 1
	end

	local XorResult1 = bit32.bxor(Digest, bit32.rshift(Digest, 15))
	local AHigh_f1, ALow_f1 = bit32.rshift(XorResult1, 16), bit32.band(XorResult1, 65535)
	Digest = bit32.lshift((AHigh_f1 * PRIME_2_LOW) + (ALow_f1 * PRIME_2_HIGH), 16) + (ALow_f1 * PRIME_2_LOW)

	local XorResult2 = bit32.bxor(Digest, bit32.rshift(Digest, 13))
	local AHigh_f2, ALow_f2 = bit32.rshift(XorResult2, 16), bit32.band(XorResult2, 65535)
	Digest = bit32.lshift((AHigh_f2 * PRIME_3_LOW) + (ALow_f2 * PRIME_3_HIGH), 16) + (ALow_f2 * PRIME_3_LOW)

	return bit32.bxor(Digest, bit32.rshift(Digest, 16))
end

local BLOCK_SIZE_BYTES = 128
local DEFAULT_OUTPUT_BYTES = 64

local BLAKE2B_MIN_OUTPUT_BYTES = 1
local BLAKE2B_MAX_OUTPUT_BYTES = 64
local BLAKE2B_MAX_KEY_BYTES = 64

local InitVectors = {
	0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
	0xf3bcc908, 0x84caa73b, 0xfe94f82b, 0x5f1d36f1, 0xade682d1, 0x2b3e6c1f, 0xfb41bd6b, 0x137e2179
}

local PERMUTATION_TABLE = {
	1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
	15, 11, 5, 9, 10, 16, 14, 7, 2, 13, 1, 3, 12, 8, 6, 4,
	12, 9, 13, 1, 6, 3, 16, 14, 11, 15, 4, 7, 8, 2, 10, 5,
	8, 10, 4, 2, 14, 13, 12, 15, 3, 7, 6, 11, 5, 1, 16, 9,
	10, 1, 6, 8, 3, 5, 11, 16, 15, 2, 12, 13, 7, 9, 4, 14,
	3, 13, 7, 11, 1, 12, 9, 4, 5, 14, 8, 6, 16, 15, 2, 10,
	13, 6, 2, 16, 15, 14, 5, 11, 1, 8, 7, 4, 10, 3, 9, 12,
	14, 12, 8, 15, 13, 2, 4, 10, 6, 1, 16, 5, 9, 7, 3, 11,
	7, 16, 15, 10, 12, 4, 1, 9, 13, 3, 14, 8, 2, 5, 11, 6,
	11, 3, 9, 5, 8, 7, 2, 6, 16, 12, 10, 15, 4, 13, 14, 1,
	1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
	15, 11, 5, 9, 10, 16, 14, 7, 2, 13, 1, 3, 12, 8, 6, 4
}

local WH9, WH10, WH11, WH12, WH13, WH14, WH15, WH16 = InitVectors[1], InitVectors[2], InitVectors[3], InitVectors[4], InitVectors[5], InitVectors[6], InitVectors[7], InitVectors[8]
local WL9, WL10, WL11, WL12, WL13, WL14, WL15, WL16 = InitVectors[9], InitVectors[10], InitVectors[11], InitVectors[12], InitVectors[13], InitVectors[14], InitVectors[15], InitVectors[16]

local function ExtractWordsFromBlock(InputBuffer: buffer, StartOffset: number, HighWords: {number}, LowWords: {number})
	for WordIdx = 1, 16 do
		local BytePos = StartOffset + (WordIdx - 1) * 8
		LowWords[WordIdx] = buffer.readu32(InputBuffer, BytePos)
		HighWords[WordIdx] = buffer.readu32(InputBuffer, BytePos + 4)
	end
end

local function ProcessCompressionRound(HighWords: {number}, LowWords: {number}, ByteCounter: number, FinalBlock: boolean, StateHigh: {number}, StateLow: {number})
	local WH1, WH2, WH3, WH4, WH5, WH6, WH7, WH8 = StateHigh[1], StateHigh[2], StateHigh[3], StateHigh[4], StateHigh[5], StateHigh[6], StateHigh[7], StateHigh[8]
	local WL1, WL2, WL3, WL4, WL5, WL6, WL7, WL8 = StateLow[1], StateLow[2], StateLow[3], StateLow[4], StateLow[5], StateLow[6], StateLow[7], StateLow[8]

	local WorkH9, WorkH10, WorkH11, WorkH12, WorkH13, WorkH14, WorkH15, WorkH16 = WH9, WH10, WH11, WH12, WH13, WH14, WH15, WH16
	local WorkL9, WorkL10, WorkL11, WorkL12, WorkL13, WorkL14, WorkL15, WorkL16 = WL9, WL10, WL11, WL12, WL13, WL14, WL15, WL16

	local XOR = bit32.bxor
	local ShiftLeft = bit32.lshift
	local ShiftRight = bit32.rshift
	local BOR = bit32.bor

	WorkH13 = XOR(WorkH13, ByteCounter // 0x100000000)
	WorkL13 = XOR(WorkL13, BOR(ByteCounter, 0))
	if FinalBlock then
		WorkH15 = bit32.bnot(WorkH15)
		WorkL15 = bit32.bnot(WorkL15)
	end

	local CarryBits, MsgHighX, MsgLowX, MsgHighY, MsgLowY = 0, 0, 0, 0, 0
	local Permutation = PERMUTATION_TABLE

	for RoundNum = 1, 12 do
		local ScheduleBase = (RoundNum - 1) * 16

		local S1, S2 = Permutation[ScheduleBase + 1], Permutation[ScheduleBase + 2]
		MsgHighX, MsgLowX = HighWords[S1], LowWords[S1]
		MsgHighY, MsgLowY = HighWords[S2], LowWords[S2]

		CarryBits = WL1 + WL5 + MsgLowX
		WH1 += WH5 + MsgHighX + CarryBits // 0x100000000
		WL1 = BOR(CarryBits, 0)

		CarryBits = WorkH13
		WorkH13 = XOR(WorkL13, WL1)
		WorkL13 = XOR(CarryBits, WH1)

		CarryBits = WorkL9 + WorkL13
		WorkH9 += WorkH13 + CarryBits // 0x100000000
		WorkL9 = BOR(CarryBits, 0)

		CarryBits = WH5
		WH5 = XOR(ShiftRight(WH5, 24), ShiftLeft(WL5, 8), ShiftRight(WorkH9, 24), ShiftLeft(WorkL9, 8))
		WL5 = XOR(ShiftRight(WL5, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL9, 24), ShiftLeft(WorkH9, 8))

		CarryBits = WL1 + WL5 + MsgLowY
		WH1 += WH5 + MsgHighY + CarryBits // 0x100000000
		WL1 = BOR(CarryBits, 0)

		CarryBits = WorkH13
		WorkH13 = XOR(ShiftRight(WorkH13, 16), ShiftLeft(WorkL13, 16), ShiftRight(WH1, 16), ShiftLeft(WL1, 16))
		WorkL13 = XOR(ShiftRight(WorkL13, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL1, 16), ShiftLeft(WH1, 16))

		CarryBits = WorkL9 + WorkL13
		WorkH9 += WorkH13 + CarryBits // 0x100000000
		WorkL9 = BOR(CarryBits, 0)

		CarryBits = WH5
		WH5 = XOR(ShiftLeft(WH5, 1), ShiftRight(WL5, 31), ShiftLeft(WorkH9, 1), ShiftRight(WorkL9, 31))
		WL5 = XOR(ShiftLeft(WL5, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL9, 1), ShiftRight(WorkH9, 31))

		local S3, S4 = Permutation[ScheduleBase + 3], Permutation[ScheduleBase + 4]
		MsgHighX, MsgLowX = HighWords[S3], LowWords[S3]
		MsgHighY, MsgLowY = HighWords[S4], LowWords[S4]

		CarryBits = WL2 + WL6 + MsgLowX
		WH2 += WH6 + MsgHighX + CarryBits // 0x100000000
		WL2 = BOR(CarryBits, 0)

		CarryBits = WorkH14
		WorkH14 = XOR(WorkL14, WL2)
		WorkL14 = XOR(CarryBits, WH2)

		CarryBits = WorkL10 + WorkL14
		WorkH10 += WorkH14 + CarryBits // 0x100000000
		WorkL10 = BOR(CarryBits, 0)

		CarryBits = WH6
		WH6 = XOR(ShiftRight(WH6, 24), ShiftLeft(WL6, 8), ShiftRight(WorkH10, 24), ShiftLeft(WorkL10, 8))
		WL6 = XOR(ShiftRight(WL6, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL10, 24), ShiftLeft(WorkH10, 8))

		CarryBits = WL2 + WL6 + MsgLowY
		WH2 += WH6 + MsgHighY + CarryBits // 0x100000000
		WL2 = BOR(CarryBits, 0)

		CarryBits = WorkH14
		WorkH14 = XOR(ShiftRight(WorkH14, 16), ShiftLeft(WorkL14, 16), ShiftRight(WH2, 16), ShiftLeft(WL2, 16))
		WorkL14 = XOR(ShiftRight(WorkL14, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL2, 16), ShiftLeft(WH2, 16))

		CarryBits = WorkL10 + WorkL14
		WorkH10 += WorkH14 + CarryBits // 0x100000000
		WorkL10 = BOR(CarryBits, 0)

		CarryBits = WH6
		WH6 = XOR(ShiftLeft(WH6, 1), ShiftRight(WL6, 31), ShiftLeft(WorkH10, 1), ShiftRight(WorkL10, 31))
		WL6 = XOR(ShiftLeft(WL6, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL10, 1), ShiftRight(WorkH10, 31))

		local S5, S6 = Permutation[ScheduleBase + 5], Permutation[ScheduleBase + 6]
		MsgHighX, MsgLowX = HighWords[S5], LowWords[S5]
		MsgHighY, MsgLowY = HighWords[S6], LowWords[S6]

		CarryBits = WL3 + WL7 + MsgLowX
		WH3 += WH7 + MsgHighX + CarryBits // 0x100000000
		WL3 = BOR(CarryBits, 0)

		CarryBits = WorkH15
		WorkH15 = XOR(WorkL15, WL3)
		WorkL15 = XOR(CarryBits, WH3)

		CarryBits = WorkL11 + WorkL15
		WorkH11 += WorkH15 + CarryBits // 0x100000000
		WorkL11 = BOR(CarryBits, 0)

		CarryBits = WH7
		WH7 = XOR(ShiftRight(WH7, 24), ShiftLeft(WL7, 8), ShiftRight(WorkH11, 24), ShiftLeft(WorkL11, 8))
		WL7 = XOR(ShiftRight(WL7, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL11, 24), ShiftLeft(WorkH11, 8))

		CarryBits = WL3 + WL7 + MsgLowY
		WH3 += WH7 + MsgHighY + CarryBits // 0x100000000
		WL3 = BOR(CarryBits, 0)

		CarryBits = WorkH15
		WorkH15 = XOR(ShiftRight(WorkH15, 16), ShiftLeft(WorkL15, 16), ShiftRight(WH3, 16), ShiftLeft(WL3, 16))
		WorkL15 = XOR(ShiftRight(WorkL15, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL3, 16), ShiftLeft(WH3, 16))

		CarryBits = WorkL11 + WorkL15
		WorkH11 += WorkH15 + CarryBits // 0x100000000
		WorkL11 = BOR(CarryBits, 0)

		CarryBits = WH7
		WH7 = XOR(ShiftLeft(WH7, 1), ShiftRight(WL7, 31), ShiftLeft(WorkH11, 1), ShiftRight(WorkL11, 31))
		WL7 = XOR(ShiftLeft(WL7, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL11, 1), ShiftRight(WorkH11, 31))

		local S7, S8 = Permutation[ScheduleBase + 7], Permutation[ScheduleBase + 8]
		MsgHighX, MsgLowX = HighWords[S7], LowWords[S7]
		MsgHighY, MsgLowY = HighWords[S8], LowWords[S8]

		CarryBits = WL4 + WL8 + MsgLowX
		WH4 += WH8 + MsgHighX + CarryBits // 0x100000000
		WL4 = BOR(CarryBits, 0)

		CarryBits = WorkH16
		WorkH16 = XOR(WorkL16, WL4)
		WorkL16 = XOR(CarryBits, WH4)

		CarryBits = WorkL12 + WorkL16
		WorkH12 += WorkH16 + CarryBits // 0x100000000
		WorkL12 = BOR(CarryBits, 0)

		CarryBits = WH8
		WH8 = XOR(ShiftRight(WH8, 24), ShiftLeft(WL8, 8), ShiftRight(WorkH12, 24), ShiftLeft(WorkL12, 8))
		WL8 = XOR(ShiftRight(WL8, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL12, 24), ShiftLeft(WorkH12, 8))

		CarryBits = WL4 + WL8 + MsgLowY
		WH4 += WH8 + MsgHighY + CarryBits // 0x100000000
		WL4 = BOR(CarryBits, 0)

		CarryBits = WorkH16
		WorkH16 = XOR(ShiftRight(WorkH16, 16), ShiftLeft(WorkL16, 16), ShiftRight(WH4, 16), ShiftLeft(WL4, 16))
		WorkL16 = XOR(ShiftRight(WorkL16, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL4, 16), ShiftLeft(WH4, 16))

		CarryBits = WorkL12 + WorkL16
		WorkH12 += WorkH16 + CarryBits // 0x100000000
		WorkL12 = BOR(CarryBits, 0)

		CarryBits = WH8
		WH8 = XOR(ShiftLeft(WH8, 1), ShiftRight(WL8, 31), ShiftLeft(WorkH12, 1), ShiftRight(WorkL12, 31))
		WL8 = XOR(ShiftLeft(WL8, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL12, 1), ShiftRight(WorkH12, 31))

		local S9, S10 = Permutation[ScheduleBase + 9], Permutation[ScheduleBase + 10]
		MsgHighX, MsgLowX = HighWords[S9], LowWords[S9]
		MsgHighY, MsgLowY = HighWords[S10], LowWords[S10]

		CarryBits = WL1 + WL6 + MsgLowX
		WH1 += WH6 + MsgHighX + CarryBits // 0x100000000
		WL1 = BOR(CarryBits, 0)

		CarryBits = WorkH16
		WorkH16 = XOR(WorkL16, WL1)
		WorkL16 = XOR(CarryBits, WH1)

		CarryBits = WorkL11 + WorkL16
		WorkH11 += WorkH16 + CarryBits // 0x100000000
		WorkL11 = BOR(CarryBits, 0)

		CarryBits = WH6
		WH6 = XOR(ShiftRight(WH6, 24), ShiftLeft(WL6, 8), ShiftRight(WorkH11, 24), ShiftLeft(WorkL11, 8))
		WL6 = XOR(ShiftRight(WL6, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL11, 24), ShiftLeft(WorkH11, 8))

		CarryBits = WL1 + WL6 + MsgLowY
		WH1 += WH6 + MsgHighY + CarryBits // 0x100000000
		WL1 = BOR(CarryBits, 0)

		CarryBits = WorkH16
		WorkH16 = XOR(ShiftRight(WorkH16, 16), ShiftLeft(WorkL16, 16), ShiftRight(WH1, 16), ShiftLeft(WL1, 16))
		WorkL16 = XOR(ShiftRight(WorkL16, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL1, 16), ShiftLeft(WH1, 16))

		CarryBits = WorkL11 + WorkL16
		WorkH11 += WorkH16 + CarryBits // 0x100000000
		WorkL11 = BOR(CarryBits, 0)

		CarryBits = WH6
		WH6 = XOR(ShiftLeft(WH6, 1), ShiftRight(WL6, 31), ShiftLeft(WorkH11, 1), ShiftRight(WorkL11, 31))
		WL6 = XOR(ShiftLeft(WL6, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL11, 1), ShiftRight(WorkH11, 31))

		local S11, S12 = Permutation[ScheduleBase + 11], Permutation[ScheduleBase + 12]
		MsgHighX, MsgLowX = HighWords[S11], LowWords[S11]
		MsgHighY, MsgLowY = HighWords[S12], LowWords[S12]

		CarryBits = WL2 + WL7 + MsgLowX
		WH2 += WH7 + MsgHighX + CarryBits // 0x100000000
		WL2 = BOR(CarryBits, 0)

		CarryBits = WorkH13
		WorkH13 = XOR(WorkL13, WL2)
		WorkL13 = XOR(CarryBits, WH2)

		CarryBits = WorkL12 + WorkL13
		WorkH12 += WorkH13 + CarryBits // 0x100000000
		WorkL12 = BOR(CarryBits, 0)

		CarryBits = WH7
		WH7 = XOR(ShiftRight(WH7, 24), ShiftLeft(WL7, 8), ShiftRight(WorkH12, 24), ShiftLeft(WorkL12, 8))
		WL7 = XOR(ShiftRight(WL7, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL12, 24), ShiftLeft(WorkH12, 8))

		CarryBits = WL2 + WL7 + MsgLowY
		WH2 += WH7 + MsgHighY + CarryBits // 0x100000000
		WL2 = BOR(CarryBits, 0)

		CarryBits = WorkH13
		WorkH13 = XOR(ShiftRight(WorkH13, 16), ShiftLeft(WorkL13, 16), ShiftRight(WH2, 16), ShiftLeft(WL2, 16))
		WorkL13 = XOR(ShiftRight(WorkL13, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL2, 16), ShiftLeft(WH2, 16))

		CarryBits = WorkL12 + WorkL13
		WorkH12 += WorkH13 + CarryBits // 0x100000000
		WorkL12 = BOR(CarryBits, 0)

		CarryBits = WH7
		WH7 = XOR(ShiftLeft(WH7, 1), ShiftRight(WL7, 31), ShiftLeft(WorkH12, 1), ShiftRight(WorkL12, 31))
		WL7 = XOR(ShiftLeft(WL7, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL12, 1), ShiftRight(WorkH12, 31))

		local S13, S14 = Permutation[ScheduleBase + 13], Permutation[ScheduleBase + 14]
		MsgHighX, MsgLowX = HighWords[S13], LowWords[S13]
		MsgHighY, MsgLowY = HighWords[S14], LowWords[S14]

		CarryBits = WL3 + WL8 + MsgLowX
		WH3 += WH8 + MsgHighX + CarryBits // 0x100000000
		WL3 = BOR(CarryBits, 0)

		CarryBits = WorkH14
		WorkH14 = XOR(WorkL14, WL3)
		WorkL14 = XOR(CarryBits, WH3)

		CarryBits = WorkL9 + WorkL14
		WorkH9 += WorkH14 + CarryBits // 0x100000000
		WorkL9 = BOR(CarryBits, 0)

		CarryBits = WH8
		WH8 = XOR(ShiftRight(WH8, 24), ShiftLeft(WL8, 8), ShiftRight(WorkH9, 24), ShiftLeft(WorkL9, 8))
		WL8 = XOR(ShiftRight(WL8, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL9, 24), ShiftLeft(WorkH9, 8))

		CarryBits = WL3 + WL8 + MsgLowY
		WH3 += WH8 + MsgHighY + CarryBits // 0x100000000
		WL3 = BOR(CarryBits, 0)

		CarryBits = WorkH14
		WorkH14 = XOR(ShiftRight(WorkH14, 16), ShiftLeft(WorkL14, 16), ShiftRight(WH3, 16), ShiftLeft(WL3, 16))
		WorkL14 = XOR(ShiftRight(WorkL14, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL3, 16), ShiftLeft(WH3, 16))

		CarryBits = WorkL9 + WorkL14
		WorkH9 += WorkH14 + CarryBits // 0x100000000
		WorkL9 = BOR(CarryBits, 0)

		CarryBits = WH8
		WH8 = XOR(ShiftLeft(WH8, 1), ShiftRight(WL8, 31), ShiftLeft(WorkH9, 1), ShiftRight(WorkL9, 31))
		WL8 = XOR(ShiftLeft(WL8, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL9, 1), ShiftRight(WorkH9, 31))

		local S15, S16 = Permutation[ScheduleBase + 15], Permutation[ScheduleBase + 16]
		MsgHighX, MsgLowX = HighWords[S15], LowWords[S15]
		MsgHighY, MsgLowY = HighWords[S16], LowWords[S16]

		CarryBits = WL4 + WL5 + MsgLowX
		WH4 += WH5 + MsgHighX + CarryBits // 0x100000000
		WL4 = BOR(CarryBits, 0)

		CarryBits = WorkH15
		WorkH15 = XOR(WorkL15, WL4)
		WorkL15 = XOR(CarryBits, WH4)

		CarryBits = WorkL10 + WorkL15
		WorkH10 += WorkH15 + CarryBits // 0x100000000
		WorkL10 = BOR(CarryBits, 0)

		CarryBits = WH5
		WH5 = XOR(ShiftRight(WH5, 24), ShiftLeft(WL5, 8), ShiftRight(WorkH10, 24), ShiftLeft(WorkL10, 8))
		WL5 = XOR(ShiftRight(WL5, 24), ShiftLeft(CarryBits, 8), ShiftRight(WorkL10, 24), ShiftLeft(WorkH10, 8))

		CarryBits = WL4 + WL5 + MsgLowY
		WH4 += WH5 + MsgHighY + CarryBits // 0x100000000
		WL4 = BOR(CarryBits, 0)

		CarryBits = WorkH15
		WorkH15 = XOR(ShiftRight(WorkH15, 16), ShiftLeft(WorkL15, 16), ShiftRight(WH4, 16), ShiftLeft(WL4, 16))
		WorkL15 = XOR(ShiftRight(WorkL15, 16), ShiftLeft(CarryBits, 16), ShiftRight(WL4, 16), ShiftLeft(WH4, 16))

		CarryBits = WorkL10 + WorkL15
		WorkH10 += WorkH15 + CarryBits // 0x100000000
		WorkL10 = BOR(CarryBits, 0)

		CarryBits = WH5
		WH5 = XOR(ShiftLeft(WH5, 1), ShiftRight(WL5, 31), ShiftLeft(WorkH10, 1), ShiftRight(WorkL10, 31))
		WL5 = XOR(ShiftLeft(WL5, 1), ShiftRight(CarryBits, 31), ShiftLeft(WorkL10, 1), ShiftRight(WorkH10, 31))
	end

	StateHigh[1] = XOR(StateHigh[1], WH1, WorkH9)
	StateLow[1] = XOR(StateLow[1], WL1, WorkL9)
	StateHigh[2] = XOR(StateHigh[2], WH2, WorkH10)
	StateLow[2] = XOR(StateLow[2], WL2, WorkL10)
	StateHigh[3] = XOR(StateHigh[3], WH3, WorkH11)
	StateLow[3] = XOR(StateLow[3], WL3, WorkL11)
	StateHigh[4] = XOR(StateHigh[4], WH4, WorkH12)
	StateLow[4] = XOR(StateLow[4], WL4, WorkL12)
	StateHigh[5] = XOR(StateHigh[5], WH5, WorkH13)
	StateLow[5] = XOR(StateLow[5], WL5, WorkL13)
	StateHigh[6] = XOR(StateHigh[6], WH6, WorkH14)
	StateLow[6] = XOR(StateLow[6], WL6, WorkL14)
	StateHigh[7] = XOR(StateHigh[7], WH7, WorkH15)
	StateLow[7] = XOR(StateLow[7], WL7, WorkL15)
	StateHigh[8] = XOR(StateHigh[8], WH8, WorkH16)
	StateLow[8] = XOR(StateLow[8], WL8, WorkL16)
end

local OutputFormat = string.rep("%08x", 16)
local function HashDigest(InputData: buffer, OutputLength: number, KeyData: buffer?): (string, buffer)
	local KeyLength = KeyData and buffer.len(KeyData) or 0
	local DataLength = buffer.len(InputData)

	local StateHigh = { WH9, WH10, WH11, WH12, WH13, WH14, WH15, WH16 }
	local StateLow = { WL9, WL10, WL11, WL12, WL13, WL14, WL15, WL16 }

	StateLow[1] = bit32.bxor(StateLow[1], 0x01010000, bit32.lshift(KeyLength, 8), OutputLength)

	local BlockHigh = table.create(16)
	local BlockLow = table.create(16)
	local ProcessedBytes = KeyLength > 0 and 128 or 0

	if KeyLength > 0 and KeyData then
		local KeyPadding = buffer.create(BLOCK_SIZE_BYTES)
		buffer.copy(KeyPadding, 0, KeyData)
		ExtractWordsFromBlock(KeyPadding, 0, BlockHigh, BlockLow)
		ProcessCompressionRound(BlockHigh, BlockLow, ProcessedBytes, DataLength == 0, StateHigh, StateLow)
	end

	local RemainingBytes = DataLength % BLOCK_SIZE_BYTES
	local FinalBlockSize = RemainingBytes == 0 and BLOCK_SIZE_BYTES or RemainingBytes

	for BlockStart = 0, DataLength - FinalBlockSize - 1, BLOCK_SIZE_BYTES do
		ExtractWordsFromBlock(InputData, BlockStart, BlockHigh, BlockLow)
		ProcessedBytes += BLOCK_SIZE_BYTES
		ProcessCompressionRound(BlockHigh, BlockLow, ProcessedBytes, false, StateHigh, StateLow)
	end

	if KeyLength == 0 or DataLength > 0 then
		local PaddedBlock = buffer.create(BLOCK_SIZE_BYTES)
		local CopyBytes = math.min(FinalBlockSize, DataLength)
		local CopyStart = math.max(0, DataLength - FinalBlockSize)
		if CopyBytes > 0 then
			buffer.copy(PaddedBlock, 0, InputData, CopyStart, CopyBytes)
		end

		ExtractWordsFromBlock(PaddedBlock, 0, BlockHigh, BlockLow)
		ProcessCompressionRound(BlockHigh, BlockLow, ProcessedBytes + CopyBytes, true, StateHigh, StateLow)
	end

	local Digest = buffer.create(OutputLength)
	local Offset = 0

	for Index = 1, 8 do
		if Offset + 4 <= OutputLength then
			buffer.writeu32(Digest, Offset, StateLow[Index])
			Offset += 4
		end

		if Offset + 4 <= OutputLength then
			buffer.writeu32(Digest, Offset, StateHigh[Index])
			Offset += 4
		end

		if Offset >= OutputLength then
			break
		end
	end

	local FinalDigest = string.format(
		OutputFormat,
		bit32.byteswap(StateLow[1]), bit32.byteswap(StateHigh[1]),
		bit32.byteswap(StateLow[2]), bit32.byteswap(StateHigh[2]),
		bit32.byteswap(StateLow[3]), bit32.byteswap(StateHigh[3]),
		bit32.byteswap(StateLow[4]), bit32.byteswap(StateHigh[4]),
		bit32.byteswap(StateLow[5]), bit32.byteswap(StateHigh[5]),
		bit32.byteswap(StateLow[6]), bit32.byteswap(StateHigh[6]),
		bit32.byteswap(StateLow[7]), bit32.byteswap(StateHigh[7]),
		bit32.byteswap(StateLow[8]), bit32.byteswap(StateHigh[8])
	)

	return string.sub(FinalDigest, 1, OutputLength * 2), Digest
end

local function BLAKE2b(InputData: buffer, OutputLength: number?, KeyData: buffer?): string
	if InputData == nil then
		error("InputData cannot be nil", 2)
	end

	if typeof(InputData) ~= "buffer" then
		error(`InputData must be a buffer, got {typeof(InputData)}`, 2)
	end

	if OutputLength then
		if typeof(OutputLength) ~= "number" then
			error(`OutputLength must be a number, got {typeof(OutputLength)}`, 2)
		end

		if OutputLength ~= math.floor(OutputLength) then
			error(`OutputLength must be an integer, got {OutputLength}`, 2)
		end

		if OutputLength < BLAKE2B_MIN_OUTPUT_BYTES or OutputLength > BLAKE2B_MAX_OUTPUT_BYTES then
			error(`OutputLength must be between {BLAKE2B_MIN_OUTPUT_BYTES} and {BLAKE2B_MAX_OUTPUT_BYTES} bytes, got {OutputLength} bytes`, 2)
		end
	end

	if KeyData then
		if typeof(KeyData) ~= "buffer" then
			error(`KeyData must be a buffer, got {typeof(KeyData)}`, 2)
		end

		local KeyLength = buffer.len(KeyData)
		if KeyLength == 0 then
			error("KeyData cannot be empty", 2)
		end

		if KeyLength > BLAKE2B_MAX_KEY_BYTES then
			error(`KeyData must be at most {BLAKE2B_MAX_KEY_BYTES} bytes long, got {KeyLength} bytes`, 2)
		end
	end

	return HashDigest(InputData, OutputLength or DEFAULT_OUTPUT_BYTES, KeyData)
end

local Blake3 = {}

local BLOCK_SIZE = 64
local CV_SIZE = 32
local EXTENDED_CV_SIZE = 64
local MAX_STACK_DEPTH = 64
local STACK_BUFFER_SIZE = MAX_STACK_DEPTH * CV_SIZE

local BLAKE3_KEY_SIZE = 32
local BLAKE3_MIN_OUTPUT_BYTES = 1
local BLAKE3_MAX_OUTPUT_BYTES = 2^32 - 1

local CHUNK_START = 0x01
local CHUNK_END = 0x02
local PARENT_FLAG = 0x04
local ROOT_FLAG = 0x08
local HASH_FLAG = 0x10
local DERIVE_CONTEXT_FLAG = 0x20
local DERIVE_MATERIAL_FLAG = 0x40

local INITIAL_VECTORS = buffer.create(CV_SIZE) do
	local IV = {
		0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
		0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
	}
	for Index, Value in ipairs(IV) do
		buffer.writeu32(INITIAL_VECTORS, (Index - 1) * 4, Value)
	end
end

local ENCODE_LOOKUP = buffer.create(256 * 2) do
	local HexChars = "0123456789abcdef"
	for Byte = 0, 255 do
		local HighNibble = bit32.rshift(Byte, 4)
		local LowNibble = Byte % 16

		local HighChar = string.byte(HexChars, HighNibble + 1)
		local LowChar = string.byte(HexChars, LowNibble + 1)

		local Combined = HighChar + bit32.lshift(LowChar, 8)
		buffer.writeu16(ENCODE_LOOKUP, Byte * 2, Combined)
	end
end

local function Compress(Hash: buffer, MessageBlock: buffer, Counter: number, V14: number, V15: number, IsFull: boolean?): buffer
	local Hash00 = buffer.readu32(Hash, 0)
	local Hash01 = buffer.readu32(Hash, 4)
	local Hash02 = buffer.readu32(Hash, 8)
	local Hash03 = buffer.readu32(Hash, 12)
	local Hash04 = buffer.readu32(Hash, 16)
	local Hash05 = buffer.readu32(Hash, 20)
	local Hash06 = buffer.readu32(Hash, 24)
	local Hash07 = buffer.readu32(Hash, 28)

	local V00, V01, V02, V03 = Hash00, Hash01, Hash02, Hash03
	local V04, V05, V06, V07 = Hash04, Hash05, Hash06, Hash07
	local V08, V09, V10, V11 = 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a

	local V12 = Counter % (2 ^ 32)
	local V13 = (Counter - V12) * (2 ^ -32)

	local M00 = buffer.readu32(MessageBlock, 0)
	local M01 = buffer.readu32(MessageBlock, 4)
	local M02 = buffer.readu32(MessageBlock, 8)
	local M03 = buffer.readu32(MessageBlock, 12)
	local M04 = buffer.readu32(MessageBlock, 16)
	local M05 = buffer.readu32(MessageBlock, 20)
	local M06 = buffer.readu32(MessageBlock, 24)
	local M07 = buffer.readu32(MessageBlock, 28)
	local M08 = buffer.readu32(MessageBlock, 32)
	local M09 = buffer.readu32(MessageBlock, 36)
	local M10 = buffer.readu32(MessageBlock, 40)
	local M11 = buffer.readu32(MessageBlock, 44)
	local M12 = buffer.readu32(MessageBlock, 48)
	local M13 = buffer.readu32(MessageBlock, 52)
	local M14 = buffer.readu32(MessageBlock, 56)
	local M15 = buffer.readu32(MessageBlock, 60)

	local XOR = bit32.bxor
	local LEFTROTATE = bit32.lrotate

	local Temp
	for Index = 1, 7 do
		V00 += V04 + M00; V12 = LEFTROTATE(XOR(V12, V00), 16)
		V08 += V12; V04 = LEFTROTATE(XOR(V04, V08), 20)
		V00 += V04 + M01; V12 = LEFTROTATE(XOR(V12, V00), 24)
		V08 += V12; V04 = LEFTROTATE(XOR(V04, V08), 25)

		V01 += V05 + M02; V13 = LEFTROTATE(XOR(V13, V01), 16)
		V09 += V13; V05 = LEFTROTATE(XOR(V05, V09), 20)
		V01 += V05 + M03; V13 = LEFTROTATE(XOR(V13, V01), 24)
		V09 += V13; V05 = LEFTROTATE(XOR(V05, V09), 25)

		V02 += V06 + M04; V14 = LEFTROTATE(XOR(V14, V02), 16)
		V10 += V14; V06 = LEFTROTATE(XOR(V06, V10), 20)
		V02 += V06 + M05; V14 = LEFTROTATE(XOR(V14, V02), 24)
		V10 += V14; V06 = LEFTROTATE(XOR(V06, V10), 25)

		V03 += V07 + M06; V15 = LEFTROTATE(XOR(V15, V03), 16)
		V11 += V15; V07 = LEFTROTATE(XOR(V07, V11), 20)
		V03 += V07 + M07; V15 = LEFTROTATE(XOR(V15, V03), 24)
		V11 += V15; V07 = LEFTROTATE(XOR(V07, V11), 25)

		V00 += V05 + M08; V15 = LEFTROTATE(XOR(V15, V00), 16)
		V10 += V15; V05 = LEFTROTATE(XOR(V05, V10), 20)
		V00 += V05 + M09; V15 = LEFTROTATE(XOR(V15, V00), 24)
		V10 += V15; V05 = LEFTROTATE(XOR(V05, V10), 25)

		V01 += V06 + M10; V12 = LEFTROTATE(XOR(V12, V01), 16)
		V11 += V12; V06 = LEFTROTATE(XOR(V06, V11), 20)
		V01 += V06 + M11; V12 = LEFTROTATE(XOR(V12, V01), 24)
		V11 += V12; V06 = LEFTROTATE(XOR(V06, V11), 25)

		V02 += V07 + M12; V13 = LEFTROTATE(XOR(V13, V02), 16)
		V08 += V13; V07 = LEFTROTATE(XOR(V07, V08), 20)
		V02 += V07 + M13; V13 = LEFTROTATE(XOR(V13, V02), 24)
		V08 += V13; V07 = LEFTROTATE(XOR(V07, V08), 25)

		V03 += V04 + M14; V14 = LEFTROTATE(XOR(V14, V03), 16)
		V09 += V14; V04 = LEFTROTATE(XOR(V04, V09), 20)
		V03 += V04 + M15; V14 = LEFTROTATE(XOR(V14, V03), 24)
		V09 += V14; V04 = LEFTROTATE(XOR(V04, V09), 25)

		if Index ~= 7 then
			Temp = M02
			M02 = M03
			M03 = M10
			M10 = M12
			M12 = M09
			M09 = M11
			M11 = M05
			M05 = M00
			M00 = Temp

			Temp = M06
			M06 = M04
			M04 = M07
			M07 = M13
			M13 = M14
			M14 = M15
			M15 = M08
			M08 = M01
			M01 = Temp
		end
	end

	if IsFull then
		local Result = buffer.create(EXTENDED_CV_SIZE)
		buffer.writeu32(Result, 0, XOR(V00, V08))
		buffer.writeu32(Result, 4, XOR(V01, V09))
		buffer.writeu32(Result, 8, XOR(V02, V10))
		buffer.writeu32(Result, 12, XOR(V03, V11))
		buffer.writeu32(Result, 16, XOR(V04, V12))
		buffer.writeu32(Result, 20, XOR(V05, V13))
		buffer.writeu32(Result, 24, XOR(V06, V14))
		buffer.writeu32(Result, 28, XOR(V07, V15))

		buffer.writeu32(Result, 32, XOR(V08, Hash00))
		buffer.writeu32(Result, 36, XOR(V09, Hash01))
		buffer.writeu32(Result, 40, XOR(V10, Hash02))
		buffer.writeu32(Result, 44, XOR(V11, Hash03))
		buffer.writeu32(Result, 48, XOR(V12, Hash04))
		buffer.writeu32(Result, 52, XOR(V13, Hash05))
		buffer.writeu32(Result, 56, XOR(V14, Hash06))
		buffer.writeu32(Result, 60, XOR(V15, Hash07))

		return Result
	else
		local Result = buffer.create(CV_SIZE)
		buffer.writeu32(Result, 0, XOR(V00, V08))
		buffer.writeu32(Result, 4, XOR(V01, V09))
		buffer.writeu32(Result, 8, XOR(V02, V10))
		buffer.writeu32(Result, 12, XOR(V03, V11))
		buffer.writeu32(Result, 16, XOR(V04, V12))
		buffer.writeu32(Result, 20, XOR(V05, V13))
		buffer.writeu32(Result, 24, XOR(V06, V14))
		buffer.writeu32(Result, 28, XOR(V07, V15))

		return Result
	end
end

local function ProcessMessage(InitialHashVector: buffer, Flags: number, Message: buffer, Length: number): buffer
	local MessageLength = buffer.len(Message)
	local StateCvs = buffer.create(STACK_BUFFER_SIZE)
	local StateCv = buffer.create(CV_SIZE)

	local StackSize = 0
	local StateCounter = 0

	local StateChunkNumber = 0
	local StateEndFlag = 0

	local BlockSize = BLOCK_SIZE
	local CvSize = CV_SIZE
	local ExtendedCvSize = EXTENDED_CV_SIZE

	local StateStartFlag = CHUNK_START
	local ChunkStart = CHUNK_START
	local ChunkEnd = CHUNK_END

	local ParentFlag = PARENT_FLAG
	local RootFlag = ROOT_FLAG
	local FlagsParent = Flags + ParentFlag

	local BlockBuffer = buffer.create(BlockSize)
	local PopCv = buffer.create(CvSize)
	local MergeBlock = buffer.create(ExtendedCvSize)
	local StackCv = buffer.create(CvSize)
	local Block = buffer.create(ExtendedCvSize)

	buffer.copy(StateCv, 0, InitialHashVector, 0, CvSize)

	for BlockOffset = 0, MessageLength - BlockSize - 1, BlockSize do
		buffer.copy(BlockBuffer, 0, Message, BlockOffset, BlockSize)
		local StateFlags = Flags + StateStartFlag + StateEndFlag
		StateCv = Compress(StateCv, BlockBuffer, StateCounter, BlockSize, StateFlags)
		StateStartFlag = 0
		StateChunkNumber += 1

		if StateChunkNumber == 15 then
			StateEndFlag = ChunkEnd
		elseif StateChunkNumber == 16 then
			local MergeCv = StateCv
			local MergeAmount = StateCounter + 1

			while MergeAmount % 2 == 0 do
				StackSize -= 1
				buffer.copy(PopCv, 0, StateCvs, StackSize * CvSize, CvSize)
				buffer.copy(MergeBlock, 0, PopCv, 0, CvSize)
				buffer.copy(MergeBlock, CvSize, MergeCv, 0, CvSize)
				MergeCv = Compress(InitialHashVector, MergeBlock, 0, BlockSize, FlagsParent)
				MergeAmount /= 2
			end

			buffer.copy(StateCvs, StackSize * CvSize, MergeCv, 0, CvSize)
			StackSize += 1

			buffer.copy(StateCv, 0, InitialHashVector, 0, CvSize)
			StateStartFlag = ChunkStart
			StateCounter += 1
			StateChunkNumber = 0
			StateEndFlag = 0
		end
	end

	local LastLength = MessageLength == 0 and 0 or ((MessageLength - 1) % BlockSize + 1)
	local PaddedMessage = buffer.create(BlockSize)
	if LastLength > 0 then
		buffer.copy(PaddedMessage, 0, Message, MessageLength - LastLength, LastLength)
	end

	local OutputCv: buffer
	local OutputBlock: buffer
	local OutputLength: number
	local OutputFlags: number

	if StateCounter > 0 then
		local StateFlags = Flags + StateStartFlag + ChunkEnd
		local MergeCv = Compress(StateCv, PaddedMessage, StateCounter, LastLength, StateFlags)
		for Index = StackSize, 2, -1 do
			buffer.copy(StackCv, 0, StateCvs, (Index - 1) * CvSize, CvSize)
			buffer.copy(Block, 0, StackCv, 0, CvSize)
			buffer.copy(Block, CvSize, MergeCv, 0, CvSize)
			MergeCv = Compress(InitialHashVector, Block, 0, BlockSize, FlagsParent)
		end

		OutputCv = InitialHashVector
		local FirstStackCv = buffer.create(CvSize)
		buffer.copy(FirstStackCv, 0, StateCvs, 0, CvSize)
		OutputBlock = buffer.create(ExtendedCvSize)

		buffer.copy(OutputBlock, 0, FirstStackCv, 0, CvSize)
		buffer.copy(OutputBlock, CvSize, MergeCv, 0, CvSize)

		OutputLength = BlockSize
		OutputFlags = Flags + RootFlag + ParentFlag
	else
		OutputCv = StateCv
		OutputBlock = PaddedMessage
		OutputLength = LastLength
		OutputFlags = Flags + StateStartFlag + ChunkEnd + RootFlag
	end

	local Output = buffer.create(Length)
	local OutputOffset = 0
	for Index = 0, Length // BlockSize do
		local MessageDigest = Compress(OutputCv, OutputBlock, Index, OutputLength, OutputFlags, true)
		local BytesToCopy = math.min(BlockSize, Length - OutputOffset)
		buffer.copy(Output, OutputOffset, MessageDigest, 0, BytesToCopy)
		OutputOffset += BytesToCopy
		if OutputOffset >= Length then
			break
		end
	end

	return Output
end

local function ToHex(Buffer: buffer): string
	local Length = buffer.len(Buffer)
	local Hex = buffer.create(Length * 2)

	local Lookup = ENCODE_LOOKUP

	local Leftover = Length % 8
	local HexCursor = 0

	for Index = 0, Length - Leftover - 1, 8 do
		local Hex1 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index) * 2)
		local Hex2 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 1) * 2)
		local Hex3 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 2) * 2)
		local Hex4 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 3) * 2)
		local Hex5 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 4) * 2)
		local Hex6 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 5) * 2)
		local Hex7 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 6) * 2)
		local Hex8 = buffer.readu16(Lookup, buffer.readu8(Buffer, Index + 7) * 2)

		buffer.writeu16(Hex, HexCursor, Hex1)
		buffer.writeu16(Hex, HexCursor + 2, Hex2)
		buffer.writeu16(Hex, HexCursor + 4, Hex3)
		buffer.writeu16(Hex, HexCursor + 6, Hex4)
		buffer.writeu16(Hex, HexCursor + 8, Hex5)
		buffer.writeu16(Hex, HexCursor + 10, Hex6)
		buffer.writeu16(Hex, HexCursor + 12, Hex7)
		buffer.writeu16(Hex, HexCursor + 14, Hex8)

		HexCursor += 16
	end

	for Index = Length - Leftover, Length - 1 do
		local HexPair = buffer.readu16(Lookup, buffer.readu8(Buffer, Index) * 2)
		buffer.writeu16(Hex, HexCursor, HexPair)
		HexCursor += 2
	end

	return buffer.tostring(Hex)
end

function Blake3.Digest(Message: buffer, Length: number?): (string, buffer)
	if Message == nil then
		error("Message cannot be nil", 2)
	end

	if typeof(Message) ~= "buffer" then
		error(`Message must be a buffer, got {typeof(Message)}`, 2)
	end

	if Length then
		if typeof(Length) ~= "number" then
			error(`Length must be a number, got {typeof(Length)}`, 2)
		end

		if Length ~= math.floor(Length) then
			error(`Length must be an integer, got {Length}`, 2)
		end

		if Length < BLAKE3_MIN_OUTPUT_BYTES then
			error(`Length must be at least {BLAKE3_MIN_OUTPUT_BYTES} byte, got {Length} bytes`, 2)
		end

		if Length > BLAKE3_MAX_OUTPUT_BYTES then
			error(`Length must be at most {BLAKE3_MAX_OUTPUT_BYTES} bytes, got {Length} bytes`, 2)
		end
	end

	local Result = ProcessMessage(INITIAL_VECTORS, 0, Message, Length or 32)

	return ToHex(Result), Result
end

function Blake3.DigestKeyed(Key: buffer, Message: buffer, Length: number?): (string, buffer)
	if Key == nil then
		error("Key cannot be nil", 2)
	end

	if typeof(Key) ~= "buffer" then
		error(`Key must be a buffer, got {typeof(Key)}`, 2)
	end

	local KeyLength = buffer.len(Key)
	if KeyLength ~= BLAKE3_KEY_SIZE then
		error(`Key must be exactly {BLAKE3_KEY_SIZE} bytes long, got {KeyLength} bytes`, 2)
	end

	if Message == nil then
		error("Message cannot be nil", 2)
	end
	if typeof(Message) ~= "buffer" then
		error(`Message must be a buffer, got {typeof(Message)}`, 2)
	end

	if Length then
		if typeof(Length) ~= "number" then
			error(`Length must be a number, got {typeof(Length)}`, 2)
		end
		if Length ~= math.floor(Length) then
			error(`Length must be an integer, got {Length}`, 2)
		end
		if Length < BLAKE3_MIN_OUTPUT_BYTES then
			error(`Length must be at least {BLAKE3_MIN_OUTPUT_BYTES} byte, got {Length} bytes`, 2)
		end
		if Length > BLAKE3_MAX_OUTPUT_BYTES then
			error(`Length must be at most {BLAKE3_MAX_OUTPUT_BYTES} bytes, got {Length} bytes`, 2)
		end
	end

	local Result = ProcessMessage(Key, HASH_FLAG, Message, Length or 32)

	return ToHex(Result), Result
end

function Blake3.DeriveKey(Context: buffer): (buffer, number?) -> (string, buffer)
	if Context == nil then
		error("Context cannot be nil", 2)
	end

	if typeof(Context) ~= "buffer" then
		error(`Context must be a buffer, got {typeof(Context)}`, 2)
	end

	local ContextHash = ProcessMessage(INITIAL_VECTORS, DERIVE_CONTEXT_FLAG, Context, 32)

	return function(Material: buffer, Length: number?): (string, buffer)
		if Material == nil then
			error("Material cannot be nil", 2)
		end

		if typeof(Material) ~= "buffer" then
			error(`Material must be a buffer, got {typeof(Material)}`, 2)
		end

		if Length then
			if typeof(Length) ~= "number" then
				error(`Length must be a number, got {typeof(Length)}`, 2)
			end

			if Length ~= math.floor(Length) then
				error(`Length must be an integer, got {Length}`, 2)
			end

			if Length < BLAKE3_MIN_OUTPUT_BYTES then
				error(`Length must be at least {BLAKE3_MIN_OUTPUT_BYTES} byte, got {Length} bytes`, 2)
			end

			if Length > BLAKE3_MAX_OUTPUT_BYTES then
				error(`Length must be at most {BLAKE3_MAX_OUTPUT_BYTES} bytes, got {Length} bytes`, 2)
			end
		end

		local Result = ProcessMessage(ContextHash, DERIVE_MATERIAL_FLAG, Material, Length or 32)

		return ToHex(Result), Result
	end
end

local function Mul32(A: number, B: number): number
	local AHigh = bit32.rshift(A, 16)
	local ALow = bit32.band(A, 0xFFFF)
	local BHigh = bit32.rshift(B, 16)
	local BLow = bit32.band(B, 0xFFFF)

	local LoLo = ALow * BLow
	local HiLo = bit32.lshift(AHigh * BLow, 16)
	local LoHi = bit32.lshift(ALow * BHigh, 16)

	local Result = bit32.bor(LoLo + HiLo, 0)
	return bit32.bor(Result + LoHi, 0)
end

local function FMix32(Hash: number): number
	Hash = Mul32(bit32.bxor(Hash, bit32.rshift(Hash, 16)), 0x85ebca6b)
	Hash = Mul32(bit32.bxor(Hash, bit32.rshift(Hash, 13)), 0xc2b2ae35)
	Hash = bit32.bxor(Hash, bit32.rshift(Hash, 16))
	return Hash
end

local function MurmurHash3(Message: buffer, Seed: number?): number
	local C1 = 0xcc9e2d51
	local C2 = 0x1b873593
	local M = 5
	local N = 0xe6546b64

	local Hash = bit32.bor(Seed or 0, 0)
	local MessageLength = buffer.len(Message)
	local BlockCount = MessageLength // 4
	local UnrolledBlocks = BlockCount // 4
	local CurrentOffset = 0

	for _ = 1, UnrolledBlocks do
		local K1 = buffer.readu32(Message, CurrentOffset)
		K1 = Mul32(bit32.lrotate(Mul32(K1, 0xcc9e2d51), 15), 0x1b873593)
		Hash = bit32.bor(bit32.lrotate(bit32.bxor(Hash, K1), 13) * 5 + 0xe6546b64, 0)

		local K2 = buffer.readu32(Message, CurrentOffset + 4)
		K2 = Mul32(bit32.lrotate(Mul32(K2, 0xcc9e2d51), 15), 0x1b873593)
		Hash = bit32.bor(bit32.lrotate(bit32.bxor(Hash, K2), 13) * 5 + 0xe6546b64, 0)

		local K3 = buffer.readu32(Message, CurrentOffset + 8)
		K3 = Mul32(bit32.lrotate(Mul32(K3, 0xcc9e2d51), 15), 0x1b873593)
		Hash = bit32.bor(bit32.lrotate(bit32.bxor(Hash, K3), 13) * 5 + 0xe6546b64, 0)

		local K4 = buffer.readu32(Message, CurrentOffset + 12)
		K4 = Mul32(bit32.lrotate(Mul32(K4, 0xcc9e2d51), 15), 0x1b873593)
		Hash = bit32.bor(bit32.lrotate(bit32.bxor(Hash, K4), 13) * 5 + 0xe6546b64, 0)

		CurrentOffset += 16
	end

	local RemainingBlocks = BlockCount % 4
	for _ = 1, RemainingBlocks do
		local K = buffer.readu32(Message, CurrentOffset)
		K = Mul32(K, 0xcc9e2d51)
		K = bit32.lrotate(K, 15)
		K = Mul32(K, 0x1b873593)
		Hash = bit32.bxor(Hash, K)
		Hash = bit32.lrotate(Hash, 13)
		Hash = bit32.bor(Hash * 5 + 0xe6546b64, 0)

		CurrentOffset += 4
	end

	local Remainder = MessageLength % 4
	if Remainder > 0 then
		local K1 = 0

		if Remainder >= 3 then
			K1 = bit32.bxor(K1, bit32.lshift(buffer.readu8(Message, CurrentOffset + 2), 16))
		end

		if Remainder >= 2 then
			K1 = bit32.bxor(K1, bit32.lshift(buffer.readu8(Message, CurrentOffset + 1), 8))
		end

		K1 = bit32.bxor(K1, buffer.readu8(Message, CurrentOffset))

		K1 = Mul32(K1, C1)
		K1 = bit32.lrotate(K1, 15)
		K1 = Mul32(K1, C2)
		Hash = bit32.bxor(Hash, K1)
	end

	Hash = bit32.bxor(Hash, MessageLength)
	Hash = FMix32(Hash)

	return Hash
end

local CRC32_LOOKUP = table.create(256)
for Index = 0, 255 do
	local CRC = Index
	for _ = 1, 8 do
		if bit32.band(CRC, 1) == 1 then
			CRC = bit32.bxor(bit32.rshift(CRC, 1), 0xEDB88320)
		else
			CRC = bit32.rshift(CRC, 1)
		end
	end

	CRC32_LOOKUP[Index + 1] = CRC
end

local function CRC32(Message: buffer, Mode: "Jam" | "Iso"?, Hex: boolean?): number | string
	local Lookup = CRC32_LOOKUP
	local Hash = 0xFFFFFFFF

	local Leftover = buffer.len(Message) % 4
	
	for Index = 0, Leftover - 1 do
		local Value = buffer.readu8(Message, Index)
		local TableIndex = bit32.band(bit32.bxor(Hash, Value), 0xFF) + 1

		Hash = bit32.bxor(
			Lookup[TableIndex],
			bit32.rshift(Hash, 8)
		)
	end
	
	for Index = Leftover, buffer.len(Message) - 1, 4 do
		local TableIndex = bit32.band(bit32.bxor(Hash, buffer.readu8(Message, Index)), 0xFF) + 1
		Hash = bit32.bxor(Lookup[TableIndex], bit32.rshift(Hash, 8))
		
		TableIndex = bit32.band(bit32.bxor(Hash, buffer.readu8(Message, Index + 1)), 0xFF) + 1
		Hash = bit32.bxor(Lookup[TableIndex], bit32.rshift(Hash, 8))
		
		TableIndex = bit32.band(bit32.bxor(Hash, buffer.readu8(Message, Index + 2)), 0xFF) + 1
		Hash = bit32.bxor(Lookup[TableIndex], bit32.rshift(Hash, 8))

		TableIndex = bit32.band(bit32.bxor(Hash, buffer.readu8(Message, Index + 3)), 0xFF) + 1
		Hash = bit32.bxor(Lookup[TableIndex], bit32.rshift(Hash, 8))
	end

	if Mode == "Jam" then
		return Hex == true and string.format("%08x", Hash) or Hash
	end

	Hash = bit32.bxor(Hash, 0xFFFFFFFF)
	return Hex == true and string.format("%08x", Hash) or Hash
end

local function Adler(Message: buffer): number
	local MOD_ALDER = 65522

	local Sum = bit32.band(bit32.rshift(MOD_ALDER, 16), 0xffff)
	MOD_ALDER = bit32.band(MOD_ALDER, 0xffff)

	local MessageLength = buffer.len(Message)

	if MessageLength == 1 then
		MOD_ALDER += buffer.readu8(Message, 0)
		if MOD_ALDER >= 65521 then
			MOD_ALDER -= 65521
		end

		Sum += MOD_ALDER
		if Sum >= 65521 then
			Sum -= 65521
		end

		return bit32.bor(MOD_ALDER, bit32.lshift(Sum, 16))
	end

	if MessageLength == 0 then
		return 0x1
	end

	local BufferPointer = 0

	if MessageLength < 16 then
		while MessageLength > 0 do
			local Value = buffer.readu8(Message, BufferPointer)

			MOD_ALDER += Value
			Sum += MOD_ALDER

			BufferPointer += 1
			MessageLength -= 1
		end

		if MOD_ALDER >= 65521 then
			MOD_ALDER -= 65521
		end
		Sum %= 65521

		return bit32.bor(MOD_ALDER, bit32.lshift(Sum, 16)) 
	end

	local NMAX = 5552
	while MessageLength >= NMAX do
		MessageLength -= NMAX

		local Iters = NMAX / 16
		while Iters > 0 do
			Iters -= 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1
		end
	end

	if MessageLength > 0 then
		while MessageLength >= 16 do
			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1

			MessageLength -= 16
		end

		while MessageLength > 0 do
			MOD_ALDER += buffer.readu8(Message, BufferPointer)
			Sum += MOD_ALDER
			BufferPointer += 1
			MessageLength -= 1
		end

		MOD_ALDER %= 65521
		Sum %= 65521
	end

	return bit32.bor(MOD_ALDER, bit32.lshift(Sum, 16))
end

type Processor = (PlaintextBlock: buffer, PlaintextOffset: number, OutputBuffer: buffer, OutputOffset: number) -> ()

local AES = {}

local SBOX_16BIT = buffer.create(131072) 
local SMIX_TABLE0 = buffer.create(65536)
local SMIX_TABLE1 = buffer.create(65536)

local INVS_XOR_TABLE = buffer.create(65536)
local INVMIX_TABLE0 = buffer.create(65536)
local INVMIX_TABLE1 = buffer.create(65536)

local KEY_CONFIGS = {
	[16] = {ExpandedLength = 176, MaterialLength = 128},
	[24] = {ExpandedLength = 208, MaterialLength = 160},
	[32] = {ExpandedLength = 240, MaterialLength = 192}
}

local SUBSTITUTION_BOX, INVERSE_SUBSTITUTION_BOX = buffer.create(256), buffer.create(256) do
	local GaloisMultiply3, GaloisMultiply9, GaloisMultiply11 = buffer.create(256), buffer.create(256), buffer.create(256)
	local function GaloisFieldMultiply(FirstValue: number, SecondValue: number): number
		local Product = 0
		for _ = 0, 7 do
			if SecondValue % 2 == 1 then
				Product = bit32.bxor(Product, FirstValue)
			end
			FirstValue = FirstValue >= 128 and bit32.bxor(FirstValue * 2 % 256, 27) or FirstValue * 2 % 256
			SecondValue = math.floor(SecondValue / 2)
		end

		return Product
	end

	local PolynomialP = 1
	local PolynomialQ = 1
	buffer.writeu8(SUBSTITUTION_BOX, 0, 99)

	for _ = 1, 255 do
		PolynomialP = bit32.bxor(PolynomialP, PolynomialP * 2, PolynomialP < 128 and 0 or 27) % 256
		PolynomialQ = bit32.bxor(PolynomialQ, PolynomialQ * 2)
		PolynomialQ = bit32.bxor(PolynomialQ, PolynomialQ * 4)
		PolynomialQ = bit32.bxor(PolynomialQ, PolynomialQ * 16) % 256
		if PolynomialQ >= 128 then
			PolynomialQ = bit32.bxor(PolynomialQ, 9)
		end

		local TempValue = bit32.bxor(
			PolynomialQ,
			PolynomialQ % 128 * 2 + PolynomialQ / 128,
			PolynomialQ % 64 * 4 + PolynomialQ / 64,
			PolynomialQ % 32 * 8 + PolynomialQ / 32,
			PolynomialQ % 16 * 16 + PolynomialQ / 16,
			99
		)
		buffer.writeu8(SUBSTITUTION_BOX, PolynomialP, TempValue)
		buffer.writeu8(INVERSE_SUBSTITUTION_BOX, TempValue, PolynomialP)
		buffer.writeu8(GaloisMultiply3, PolynomialP, GaloisFieldMultiply(3, PolynomialP))
		buffer.writeu8(GaloisMultiply9, PolynomialP, GaloisFieldMultiply(9, PolynomialP))
		buffer.writeu8(GaloisMultiply11, PolynomialP, GaloisFieldMultiply(11, PolynomialP))
	end

	local TableIndex = 0
	for OuterIndex = 0, 255 do
		local PolynomialPOuter = buffer.readu8(SUBSTITUTION_BOX, OuterIndex)
		local PolynomialPBytes = PolynomialPOuter * 256
		local Galois2 = GaloisFieldMultiply(2, PolynomialPOuter)
		local Galois13 = GaloisFieldMultiply(13, OuterIndex)
		local Galois14 = GaloisFieldMultiply(14, OuterIndex)

		for InnerIndex = 0, 255 do
			local PolynomialQInner = buffer.readu8(SUBSTITUTION_BOX, InnerIndex)

			buffer.writeu16(SBOX_16BIT, TableIndex * 2, PolynomialPBytes + PolynomialQInner)
			buffer.writeu8(INVS_XOR_TABLE, TableIndex, buffer.readu8(INVERSE_SUBSTITUTION_BOX, bit32.bxor(OuterIndex, InnerIndex)))
			buffer.writeu8(SMIX_TABLE0, TableIndex, bit32.bxor(Galois2, buffer.readu8(GaloisMultiply3, PolynomialQInner)))
			buffer.writeu8(SMIX_TABLE1, TableIndex, bit32.bxor(PolynomialPOuter, PolynomialQInner))
			buffer.writeu8(INVMIX_TABLE0, TableIndex, bit32.bxor(Galois14, buffer.readu8(GaloisMultiply11, InnerIndex)))
			buffer.writeu8(INVMIX_TABLE1, TableIndex, bit32.bxor(Galois13, buffer.readu8(GaloisMultiply9, InnerIndex)))
			TableIndex += 1
		end
	end
end

local function ExpandKeySchedule(Key: buffer, KeyLength: number, OutputBuffer: buffer): buffer
	buffer.copy(OutputBuffer, 0, Key, 0, KeyLength)

	local Word = bit32.rrotate(buffer.readu32(OutputBuffer, KeyLength - 4), 8)
	local RoundConstant = 0.5
	local SBox_16 = SBOX_16BIT

	if KeyLength == 32 then
		for KeyOffset = 32, 192, 32 do
			RoundConstant = RoundConstant * 2 % 229
			local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536 + buffer.readu16(SBox_16, Word % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 32), SBoxLookup, RoundConstant)
			buffer.writeu32(OutputBuffer, KeyOffset, Word)

			local W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 28), Word)
			buffer.writeu32(OutputBuffer, KeyOffset + 4, W1)
			local W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 24), W1)
			buffer.writeu32(OutputBuffer, KeyOffset + 8, W2)
			local W3 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 20), W2)
			buffer.writeu32(OutputBuffer, KeyOffset + 12, W3)

			SBoxLookup = buffer.readu16(SBox_16, W3 // 65536 * 2) * 65536 + buffer.readu16(SBox_16, W3 % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 16), SBoxLookup)
			buffer.writeu32(OutputBuffer, KeyOffset + 16, Word)

			W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 12), Word)
			buffer.writeu32(OutputBuffer, KeyOffset + 20, W1)
			W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 8), W1)
			buffer.writeu32(OutputBuffer, KeyOffset + 24, W2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 4), W2)
			buffer.writeu32(OutputBuffer, KeyOffset + 28, Word)
			Word = bit32.rrotate(Word, 8)
		end

		local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536 + buffer.readu16(SBox_16, Word % 65536 * 2)
		Word = bit32.bxor(buffer.readu32(OutputBuffer, 192), SBoxLookup, 64)
		buffer.writeu32(OutputBuffer, 224, Word)

		local W1 = bit32.bxor(buffer.readu32(OutputBuffer, 196), Word)
		buffer.writeu32(OutputBuffer, 228, W1)
		local W2 = bit32.bxor(buffer.readu32(OutputBuffer, 200), W1)
		buffer.writeu32(OutputBuffer, 232, W2)
		buffer.writeu32(OutputBuffer, 236, bit32.bxor(buffer.readu32(OutputBuffer, 204), W2))

	elseif KeyLength == 24 then
		for KeyOffset = 24, 168, 24 do
			RoundConstant = RoundConstant * 2 % 229
			local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536 + buffer.readu16(SBox_16, Word % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 24), SBoxLookup, RoundConstant)
			buffer.writeu32(OutputBuffer, KeyOffset, Word)

			local W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 20), Word)
			buffer.writeu32(OutputBuffer, KeyOffset + 4, W1)
			local W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 16), W1)
			buffer.writeu32(OutputBuffer, KeyOffset + 8, W2)
			local W3 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 12), W2)
			buffer.writeu32(OutputBuffer, KeyOffset + 12, W3)
			local W4 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 8), W3)
			buffer.writeu32(OutputBuffer, KeyOffset + 16, W4)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 4), W4)
			buffer.writeu32(OutputBuffer, KeyOffset + 20, Word)
			Word = bit32.rrotate(Word, 8)
		end

		local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536 + buffer.readu16(SBox_16, Word % 65536 * 2)
		Word = bit32.bxor(buffer.readu32(OutputBuffer, 168), SBoxLookup, 128)
		buffer.writeu32(OutputBuffer, 192, Word)

		local W1 = bit32.bxor(buffer.readu32(OutputBuffer, 172), Word)
		buffer.writeu32(OutputBuffer, 196, W1)
		local W2 = bit32.bxor(buffer.readu32(OutputBuffer, 176), W1)
		buffer.writeu32(OutputBuffer, 200, W2)
		buffer.writeu32(OutputBuffer, 204, bit32.bxor(buffer.readu32(OutputBuffer, 180), W2))
	else
		for KeyOffset = 16, 144, 16 do
			RoundConstant = RoundConstant * 2 % 229
			local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536 + buffer.readu16(SBox_16, Word % 65536 * 2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 16), SBoxLookup, RoundConstant)
			buffer.writeu32(OutputBuffer, KeyOffset, Word)

			local W1 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 12), Word)
			buffer.writeu32(OutputBuffer, KeyOffset + 4, W1)
			local W2 = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 8), W1)
			buffer.writeu32(OutputBuffer, KeyOffset + 8, W2)
			Word = bit32.bxor(buffer.readu32(OutputBuffer, KeyOffset - 4), W2)
			buffer.writeu32(OutputBuffer, KeyOffset + 12, Word)
			Word = bit32.rrotate(Word, 8)
		end

		local SBoxLookup = buffer.readu16(SBox_16, Word // 65536 * 2) * 65536 + buffer.readu16(SBox_16, Word % 65536 * 2)
		Word = bit32.bxor(buffer.readu32(OutputBuffer, 144), SBoxLookup, 54)
		buffer.writeu32(OutputBuffer, 160, Word)

		local W1 = bit32.bxor(buffer.readu32(OutputBuffer, 148), Word)
		buffer.writeu32(OutputBuffer, 164, W1)
		local W2 = bit32.bxor(buffer.readu32(OutputBuffer, 152), W1)
		buffer.writeu32(OutputBuffer, 168, W2)
		buffer.writeu32(OutputBuffer, 172, bit32.bxor(buffer.readu32(OutputBuffer, 156), W2))
	end

	return OutputBuffer
end

local A0: number, A1: number, A2: number, A3: number, A4: number, A5: number, A6: number, A7: number, A8: number, A9: number, A10: number, A11: number, A12: number, A13: number, A14: number, A15: number
local function EncryptBlock(RoundKeys: buffer, MaterialLength: number, Plaintext: buffer, PlaintextOffset: number, Output: buffer, OutputOffset: number)
	A0 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset), buffer.readu8(RoundKeys, 0))
	A1 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 1), buffer.readu8(RoundKeys, 1))
	A2 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 2), buffer.readu8(RoundKeys, 2))
	A3 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 3), buffer.readu8(RoundKeys, 3))
	A4 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 4), buffer.readu8(RoundKeys, 4))
	A5 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 5), buffer.readu8(RoundKeys, 5))
	A6 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 6), buffer.readu8(RoundKeys, 6))
	A7 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 7), buffer.readu8(RoundKeys, 7))
	A8 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 8), buffer.readu8(RoundKeys, 8))
	A9 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 9), buffer.readu8(RoundKeys, 9))
	A10 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 10), buffer.readu8(RoundKeys, 10))
	A11 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 11), buffer.readu8(RoundKeys, 11))
	A12 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 12), buffer.readu8(RoundKeys, 12))
	A13 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 13), buffer.readu8(RoundKeys, 13))
	A14 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 14), buffer.readu8(RoundKeys, 14))
	A15 = bit32.bxor(buffer.readu8(Plaintext, PlaintextOffset + 15), buffer.readu8(RoundKeys, 15))

	local B0: number, B1: number, B2: number, B3: number, B4: number, B5: number, B6: number, B7: number, B8: number, B9: number, B10: number, B11: number, B12: number, B13: number, B14: number, B15: number
		= A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15

	local I0: number = B0 * 256 + B5; local I1: number = B5 * 256 + B10; local I2: number = B10 * 256 + B15; local I3: number = B15 * 256 + B0
	local I4: number = B4 * 256 + B9; local I5: number = B9 * 256 + B14; local I6: number = B14 * 256 + B3; local I7: number = B3 * 256 + B4
	local I8: number = B8 * 256 + B13; local I9: number = B13 * 256 + B2; local I10: number = B2 * 256 + B7; local I11: number = B7 * 256 + B8
	local I12: number = B12 * 256 + B1; local I13: number = B1 * 256 + B6; local I14: number = B6 * 256 + B11; local I15: number = B11 * 256 + B12

	local Tbl0, Tbl1 = SMIX_TABLE0, SMIX_TABLE1
	for RoundOffset = 16, MaterialLength, 16 do
		B0 = bit32.bxor(buffer.readu8(Tbl0, I0), buffer.readu8(Tbl1, I2), buffer.readu8(RoundKeys, RoundOffset))
		B1 = bit32.bxor(buffer.readu8(Tbl0, I1), buffer.readu8(Tbl1, I3), buffer.readu8(RoundKeys, RoundOffset + 1))
		B2 = bit32.bxor(buffer.readu8(Tbl0, I2), buffer.readu8(Tbl1, I0), buffer.readu8(RoundKeys, RoundOffset + 2))
		B3 = bit32.bxor(buffer.readu8(Tbl0, I3), buffer.readu8(Tbl1, I1), buffer.readu8(RoundKeys, RoundOffset + 3))
		B4 = bit32.bxor(buffer.readu8(Tbl0, I4), buffer.readu8(Tbl1, I6), buffer.readu8(RoundKeys, RoundOffset + 4))
		B5 = bit32.bxor(buffer.readu8(Tbl0, I5), buffer.readu8(Tbl1, I7), buffer.readu8(RoundKeys, RoundOffset + 5))
		B6 = bit32.bxor(buffer.readu8(Tbl0, I6), buffer.readu8(Tbl1, I4), buffer.readu8(RoundKeys, RoundOffset + 6))
		B7 = bit32.bxor(buffer.readu8(Tbl0, I7), buffer.readu8(Tbl1, I5), buffer.readu8(RoundKeys, RoundOffset + 7))
		B8 = bit32.bxor(buffer.readu8(Tbl0, I8), buffer.readu8(Tbl1, I10), buffer.readu8(RoundKeys, RoundOffset + 8))
		B9 = bit32.bxor(buffer.readu8(Tbl0, I9), buffer.readu8(Tbl1, I11), buffer.readu8(RoundKeys, RoundOffset + 9))
		B10 = bit32.bxor(buffer.readu8(Tbl0, I10), buffer.readu8(Tbl1, I8), buffer.readu8(RoundKeys, RoundOffset + 10))
		B11 = bit32.bxor(buffer.readu8(Tbl0, I11), buffer.readu8(Tbl1, I9), buffer.readu8(RoundKeys, RoundOffset + 11))
		B12 = bit32.bxor(buffer.readu8(Tbl0, I12), buffer.readu8(Tbl1, I14), buffer.readu8(RoundKeys, RoundOffset + 12))
		B13 = bit32.bxor(buffer.readu8(Tbl0, I13), buffer.readu8(Tbl1, I15), buffer.readu8(RoundKeys, RoundOffset + 13))
		B14 = bit32.bxor(buffer.readu8(Tbl0, I14), buffer.readu8(Tbl1, I12), buffer.readu8(RoundKeys, RoundOffset + 14))
		B15 = bit32.bxor(buffer.readu8(Tbl0, I15), buffer.readu8(Tbl1, I13), buffer.readu8(RoundKeys, RoundOffset + 15))

		I0, I1, I2, I3 = B0 * 256 + B5, B5 * 256 + B10, B10 * 256 + B15, B15 * 256 + B0
		I4, I5, I6, I7 = B4 * 256 + B9, B9 * 256 + B14, B14 * 256 + B3, B3 * 256 + B4
		I8, I9, I10, I11 = B8 * 256 + B13, B13 * 256 + B2, B2 * 256 + B7, B7 * 256 + B8
		I12, I13, I14, I15 = B12 * 256 + B1, B1 * 256 + B6, B6 * 256 + B11, B11 * 256 + B12
	end

	buffer.writeu32(Output, OutputOffset, bit32.bxor(
		buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I15), buffer.readu8(SMIX_TABLE1, I13), buffer.readu8(RoundKeys, MaterialLength + 31)) * 512 + 
			bit32.bxor(buffer.readu8(Tbl0, I10), buffer.readu8(SMIX_TABLE1, I8), buffer.readu8(RoundKeys, MaterialLength + 26)) * 2) * 65536 + 
			buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I5), buffer.readu8(SMIX_TABLE1, I7), buffer.readu8(RoundKeys, MaterialLength + 21)) * 512 + 
				bit32.bxor(buffer.readu8(Tbl0, I0), buffer.readu8(SMIX_TABLE1, I2), buffer.readu8(RoundKeys, MaterialLength + 16)) * 2),
		buffer.readu32(RoundKeys, MaterialLength + 32)
		))

	buffer.writeu32(Output, OutputOffset + 4, bit32.bxor(
		buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I3), buffer.readu8(SMIX_TABLE1, I1), buffer.readu8(RoundKeys, MaterialLength + 19)) * 512 + 
			bit32.bxor(buffer.readu8(Tbl0, I14), buffer.readu8(SMIX_TABLE1, I12), buffer.readu8(RoundKeys, MaterialLength + 30)) * 2) * 65536 + 
			buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I9), buffer.readu8(SMIX_TABLE1, I11), buffer.readu8(RoundKeys, MaterialLength + 25)) * 512 + 
				bit32.bxor(buffer.readu8(Tbl0, I4), buffer.readu8(SMIX_TABLE1, I6), buffer.readu8(RoundKeys, MaterialLength + 20)) * 2),
		buffer.readu32(RoundKeys, MaterialLength + 36)
		))

	buffer.writeu32(Output, OutputOffset + 8, bit32.bxor(
		buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I7), buffer.readu8(SMIX_TABLE1, I5), buffer.readu8(RoundKeys, MaterialLength + 23)) * 512 + 
			bit32.bxor(buffer.readu8(Tbl0, I2), buffer.readu8(SMIX_TABLE1, I0), buffer.readu8(RoundKeys, MaterialLength + 18)) * 2) * 65536 + 
			buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I13), buffer.readu8(SMIX_TABLE1, I15), buffer.readu8(RoundKeys, MaterialLength + 29)) * 512 + 
				bit32.bxor(buffer.readu8(Tbl0, I8), buffer.readu8(SMIX_TABLE1, I10), buffer.readu8(RoundKeys, MaterialLength + 24)) * 2),
		buffer.readu32(RoundKeys, MaterialLength + 40)
		))

	buffer.writeu32(Output, OutputOffset + 12, bit32.bxor(
		buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I11), buffer.readu8(SMIX_TABLE1, I9), buffer.readu8(RoundKeys, MaterialLength + 27)) * 512 + 
			bit32.bxor(buffer.readu8(Tbl0, I6), buffer.readu8(SMIX_TABLE1, I4), buffer.readu8(RoundKeys, MaterialLength + 22)) * 2) * 65536 + 
			buffer.readu16(SBOX_16BIT, bit32.bxor(buffer.readu8(Tbl0, I1), buffer.readu8(SMIX_TABLE1, I3), buffer.readu8(RoundKeys, MaterialLength + 17)) * 512 + 
				bit32.bxor(buffer.readu8(Tbl0, I12), buffer.readu8(SMIX_TABLE1, I14), buffer.readu8(RoundKeys, MaterialLength + 28)) * 2),
		buffer.readu32(RoundKeys, MaterialLength + 44)
		))
end

local function ConstantTimeCompare(Buffer1: buffer, Buffer2: buffer): boolean
	local Length1 = buffer.len(Buffer1)
	local Length2 = buffer.len(Buffer2)
	if Length1 ~= Length2 then
		return false
	end

	local Difference = 0
	for Index = 0, Length1 - 1 do
		Difference = bit32.bor(Difference, bit32.bxor(
			buffer.readu8(Buffer1, Index),
			buffer.readu8(Buffer2, Index)
			))
	end

	return Difference == 0
end

local function GfMult(X: buffer, Y: buffer, Z: buffer)
	local V = buffer.create(16)

	buffer.writeu32(Z, 0, 0)
	buffer.writeu32(Z, 4, 0)
	buffer.writeu32(Z, 8, 0)
	buffer.writeu32(Z, 12, 0)

	buffer.writeu32(V, 0, buffer.readu32(Y, 0))
	buffer.writeu32(V, 4, buffer.readu32(Y, 4))
	buffer.writeu32(V, 8, buffer.readu32(Y, 8))
	buffer.writeu32(V, 12, buffer.readu32(Y, 12))

	for I = 0, 15 do
		for J = 0, 7 do
			if bit32.band(buffer.readu8(X, I), bit32.lshift(1, 7 - J)) ~= 0 then
				buffer.writeu32(Z, 0, bit32.bxor(buffer.readu32(Z, 0), buffer.readu32(V, 0)))
				buffer.writeu32(Z, 4, bit32.bxor(buffer.readu32(Z, 4), buffer.readu32(V, 4)))
				buffer.writeu32(Z, 8, bit32.bxor(buffer.readu32(Z, 8), buffer.readu32(V, 8)))
				buffer.writeu32(Z, 12, bit32.bxor(buffer.readu32(Z, 12), buffer.readu32(V, 12)))
			end

			if buffer.readu8(V, 15) % 2 == 1 then
				local Val: number = 0

				Val = bit32.byteswap(buffer.readu32(V, 12))
				Val = bit32.rshift(Val, 1)
				if bit32.band(buffer.readu8(V, 11), 0x01) ~= 0 then
					Val = bit32.bor(Val, 0x80000000)
				end
				buffer.writeu32(V, 12, bit32.byteswap(Val))

				Val = bit32.byteswap(buffer.readu32(V, 8))
				Val = bit32.rshift(Val, 1)
				if bit32.band(buffer.readu8(V, 7), 0x01) ~= 0 then
					Val = bit32.bor(Val, 0x80000000)
				end
				buffer.writeu32(V, 8, bit32.byteswap(Val))

				Val = bit32.byteswap(buffer.readu32(V, 4))
				Val = bit32.rshift(Val, 1)
				if bit32.band(buffer.readu8(V, 3), 0x01) ~= 0 then
					Val = bit32.bor(Val, 0x80000000)
				end
				buffer.writeu32(V, 4, bit32.byteswap(Val))

				Val = bit32.byteswap(buffer.readu32(V, 0))
				Val = bit32.rshift(Val, 1)
				buffer.writeu32(V, 0, bit32.byteswap(Val))

				buffer.writeu8(V, 0, bit32.bxor(buffer.readu8(V, 0), 0xE1))
			else
				local Val: number = 0

				Val = bit32.byteswap(buffer.readu32(V, 12))
				Val = bit32.rshift(Val, 1)
				if bit32.band(buffer.readu8(V, 11), 0x01) ~= 0 then
					Val = bit32.bor(Val, 0x80000000)
				end
				buffer.writeu32(V, 12, bit32.byteswap(Val))

				Val = bit32.byteswap(buffer.readu32(V, 8))
				Val = bit32.rshift(Val, 1)
				if bit32.band(buffer.readu8(V, 7), 0x01) ~= 0 then
					Val = bit32.bor(Val, 0x80000000)
				end
				buffer.writeu32(V, 8, bit32.byteswap(Val))

				Val = bit32.byteswap(buffer.readu32(V, 4))
				Val = bit32.rshift(Val, 1)
				if bit32.band(buffer.readu8(V, 3), 0x01) ~= 0 then
					Val = bit32.bor(Val, 0x80000000)
				end
				buffer.writeu32(V, 4, bit32.byteswap(Val))

				Val = bit32.byteswap(buffer.readu32(V, 0))
				Val = bit32.rshift(Val, 1)
				buffer.writeu32(V, 0, bit32.byteswap(Val))
			end
		end
	end
end

local function Ghash(H: buffer, X: buffer, XLen: number, Y: buffer)
	local M = math.floor(XLen / 16)
	local XPos = 0
	local Tmp = buffer.create(16)

	for I = 0, M - 1 do
		buffer.writeu32(Y, 0, bit32.bxor(buffer.readu32(Y, 0), buffer.readu32(X, XPos)))
		buffer.writeu32(Y, 4, bit32.bxor(buffer.readu32(Y, 4), buffer.readu32(X, XPos + 4)))
		buffer.writeu32(Y, 8, bit32.bxor(buffer.readu32(Y, 8), buffer.readu32(X, XPos + 8)))
		buffer.writeu32(Y, 12, bit32.bxor(buffer.readu32(Y, 12), buffer.readu32(X, XPos + 12)))
		XPos += 16

		GfMult(Y, H, Tmp)
		buffer.writeu32(Y, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(Y, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(Y, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(Y, 12, buffer.readu32(Tmp, 12))
	end

	if XPos < XLen then
		local Last = XLen - XPos
		buffer.writeu32(Tmp, 0, 0)
		buffer.writeu32(Tmp, 4, 0)
		buffer.writeu32(Tmp, 8, 0)
		buffer.writeu32(Tmp, 12, 0)

		for I = 0, Last - 1 do
			buffer.writeu8(Tmp, I, buffer.readu8(X, XPos + I))
		end

		buffer.writeu32(Y, 0, bit32.bxor(buffer.readu32(Y, 0), buffer.readu32(Tmp, 0)))
		buffer.writeu32(Y, 4, bit32.bxor(buffer.readu32(Y, 4), buffer.readu32(Tmp, 4)))
		buffer.writeu32(Y, 8, bit32.bxor(buffer.readu32(Y, 8), buffer.readu32(Tmp, 8)))
		buffer.writeu32(Y, 12, bit32.bxor(buffer.readu32(Y, 12), buffer.readu32(Tmp, 12)))

		GfMult(Y, H, Tmp)

		buffer.writeu32(Y, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(Y, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(Y, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(Y, 12, buffer.readu32(Tmp, 12))
	end
end

local function Gctr(EncryptionProcessor: Processor, ICB: buffer, X: buffer, XLen: number, Y: buffer)
	if XLen == 0 then
		return
	end

	local N = math.floor(XLen / 16)
	local CB = buffer.create(16)
	local Tmp = buffer.create(16)
	local XPos = 0
	local YPos = 0

	buffer.writeu32(CB, 0, buffer.readu32(ICB, 0))
	buffer.writeu32(CB, 4, buffer.readu32(ICB, 4))
	buffer.writeu32(CB, 8, buffer.readu32(ICB, 8))
	buffer.writeu32(CB, 12, buffer.readu32(ICB, 12))

	for I = 0, N - 1 do
		EncryptionProcessor(CB, 0, Tmp, 0)

		buffer.writeu32(Y, YPos + 0, bit32.bxor(buffer.readu32(X, XPos + 0), buffer.readu32(Tmp, 0)))
		buffer.writeu32(Y, YPos + 4, bit32.bxor(buffer.readu32(X, XPos + 4), buffer.readu32(Tmp, 4)))
		buffer.writeu32(Y, YPos + 8, bit32.bxor(buffer.readu32(X, XPos + 8), buffer.readu32(Tmp, 8)))
		buffer.writeu32(Y, YPos + 12, bit32.bxor(buffer.readu32(X, XPos + 12), buffer.readu32(Tmp, 12)))

		XPos += 16
		YPos += 16

		local Val = bit32.byteswap(buffer.readu32(CB, 12))
		Val = (Val + 1) % 0x100000000
		buffer.writeu32(CB, 12, bit32.byteswap(Val))
	end

	local Last = XLen - XPos
	if Last > 0 then
		EncryptionProcessor(CB, 0, Tmp, 0)
		for I = 0, Last - 1 do
			local XByte = buffer.readu8(X, XPos + I)
			local TmpByte = buffer.readu8(Tmp, I)
			buffer.writeu8(Y, YPos + I, bit32.bxor(XByte, TmpByte))
		end
	end
end

local function PrepareJ0(IV: buffer, IVLen: number, H: buffer, J0: buffer)
	if IVLen == 12 then
		buffer.writeu32(J0, 0, buffer.readu32(IV, 0))
		buffer.writeu32(J0, 4, buffer.readu32(IV, 4))
		buffer.writeu32(J0, 8, buffer.readu32(IV, 8))
		buffer.writeu32(J0, 12, 0x01000000)
	else
		buffer.writeu32(J0, 0, 0)
		buffer.writeu32(J0, 4, 0)
		buffer.writeu32(J0, 8, 0)
		buffer.writeu32(J0, 12, 0)

		Ghash(H, IV, IVLen, J0)

		local LenBuf = buffer.create(16)
		local IVLenBits = IVLen * 8

		buffer.writeu32(LenBuf, 0, 0) 
		buffer.writeu32(LenBuf, 4, 0)
		buffer.writeu32(LenBuf, 8, 0)
		buffer.writeu32(LenBuf, 12, IVLenBits)

		Ghash(H, LenBuf, 16, J0)
	end
end

local function GcmGctr(EncryptionProcessor: Processor, J0: buffer, Input: buffer, Len: number, Output: buffer)
	if Len == 0 then
		return
	end

	local J0Inc = buffer.create(16)

	buffer.writeu32(J0Inc, 0, buffer.readu32(J0, 0))
	buffer.writeu32(J0Inc, 4, buffer.readu32(J0, 4))
	buffer.writeu32(J0Inc, 8, buffer.readu32(J0, 8))
	buffer.writeu32(J0Inc, 12, buffer.readu32(J0, 12))

	local Val = bit32.byteswap(buffer.readu32(J0Inc, 12))
	Val = (Val + 1) % 0x100000000
	buffer.writeu32(J0Inc, 12, bit32.byteswap(Val))

	Gctr(EncryptionProcessor, J0Inc, Input, Len, Output)
end

local function GcmHash(H: buffer, AAD: buffer, AADLen: number, Crypt: buffer, CryptLen: number, S: buffer)
	local LenBuf = buffer.create(16)

	buffer.writeu32(S, 0, 0)
	buffer.writeu32(S, 4, 0)
	buffer.writeu32(S, 8, 0)
	buffer.writeu32(S, 12, 0)

	local M = math.floor(AADLen / 16)
	local XPos = 0
	local Tmp = buffer.create(16)

	for I = 0, M - 1 do
		buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(AAD, XPos)))
		buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(AAD, XPos + 4)))
		buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(AAD, XPos + 8)))
		buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(AAD, XPos + 12)))
		XPos += 16

		GfMult(S, H, Tmp)

		buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
	end

	if XPos < AADLen then
		local Last = AADLen - XPos

		buffer.writeu32(Tmp, 0, 0)
		buffer.writeu32(Tmp, 4, 0)
		buffer.writeu32(Tmp, 8, 0)
		buffer.writeu32(Tmp, 12, 0)

		for I = 0, Last - 1 do
			buffer.writeu8(Tmp, I, buffer.readu8(AAD, XPos + I))
		end

		buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(Tmp, 0)))
		buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(Tmp, 4)))
		buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(Tmp, 8)))
		buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(Tmp, 12)))

		GfMult(S, H, Tmp)

		buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
	end

	M = math.floor(CryptLen / 16)
	XPos = 0

	for I = 0, M - 1 do
		buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(Crypt, XPos)))
		buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(Crypt, XPos + 4)))
		buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(Crypt, XPos + 8)))
		buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(Crypt, XPos + 12)))
		XPos += 16

		GfMult(S, H, Tmp)
		buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
	end

	if XPos < CryptLen then
		local Last = CryptLen - XPos
		buffer.writeu32(Tmp, 0, 0)
		buffer.writeu32(Tmp, 4, 0)
		buffer.writeu32(Tmp, 8, 0)
		buffer.writeu32(Tmp, 12, 0)

		for I = 0, Last - 1 do
			buffer.writeu8(Tmp, I, buffer.readu8(Crypt, XPos + I))
		end

		buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(Tmp, 0)))
		buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(Tmp, 4)))
		buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(Tmp, 8)))
		buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(Tmp, 12)))

		GfMult(S, H, Tmp)

		buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
	end

	local AADLenBits = AADLen * 8
	local CryptLenBits = CryptLen * 8

	buffer.writeu32(LenBuf, 0, 0)
	buffer.writeu32(LenBuf, 4, bit32.byteswap(AADLenBits))

	buffer.writeu32(LenBuf, 8, 0)
	buffer.writeu32(LenBuf, 12, bit32.byteswap(CryptLenBits))

	M = 1
	XPos = 0

	for I = 0, M - 1 do
		buffer.writeu32(S, 0, bit32.bxor(buffer.readu32(S, 0), buffer.readu32(LenBuf, XPos)))
		buffer.writeu32(S, 4, bit32.bxor(buffer.readu32(S, 4), buffer.readu32(LenBuf, XPos + 4)))
		buffer.writeu32(S, 8, bit32.bxor(buffer.readu32(S, 8), buffer.readu32(LenBuf, XPos + 8)))
		buffer.writeu32(S, 12, bit32.bxor(buffer.readu32(S, 12), buffer.readu32(LenBuf, XPos + 12)))
		XPos += 16

		GfMult(S, H, Tmp)

		buffer.writeu32(S, 0, buffer.readu32(Tmp, 0))
		buffer.writeu32(S, 4, buffer.readu32(Tmp, 4))
		buffer.writeu32(S, 8, buffer.readu32(Tmp, 8))
		buffer.writeu32(S, 12, buffer.readu32(Tmp, 12))
	end
end

function AES.Encrypt(Key: buffer, IV: buffer, Plaintext: buffer, AAD: buffer?): (buffer, buffer)
	if not Key or typeof(Key) ~= "buffer" then
		error("Key must be a buffer", 2)
	end
	if not IV or typeof(IV) ~= "buffer" then
		error("IV must be a buffer", 2)
	end
	if not Plaintext or typeof(Plaintext) ~= "buffer" then
		error("Plaintext must be a buffer", 2)
	end

	local KeyLength = buffer.len(Key)
	if KeyLength ~= 16 and KeyLength ~= 24 and KeyLength ~= 32 then
		error("Key must be 16, 24, or 32 bytes", 2)
	end

	local RoundKeysBuffer = ExpandKeySchedule(Key, KeyLength, buffer.create(KEY_CONFIGS[KeyLength].ExpandedLength))
	local KeyMaterialLength = KEY_CONFIGS[KeyLength].MaterialLength

	local function EncryptionProcessor(PlaintextBlock: buffer, PlaintextOffset: number, OutputBuffer: buffer, OutputOffset: number)
		EncryptBlock(RoundKeysBuffer, KeyMaterialLength, PlaintextBlock, PlaintextOffset, OutputBuffer, OutputOffset)
	end

	local IVLen = buffer.len(IV)
	local AADLen = buffer.len(AAD or buffer.create(0))
	local PlainLen = buffer.len(Plaintext)
	local AuthData = AAD or buffer.create(0)

	local OutputBuffer = buffer.create(PlainLen)

	local H = buffer.create(16)
	local J0 = buffer.create(16)
	local S = buffer.create(16)

	EncryptionProcessor(H, 0, H, 0)
	PrepareJ0(IV, IVLen, H, J0)
	GcmGctr(EncryptionProcessor, J0, Plaintext, PlainLen, OutputBuffer)
	GcmHash(H, AuthData, AADLen, OutputBuffer, PlainLen, S)

	return OutputBuffer
end

function AES.Decrypt(Key: buffer, IV: buffer, Ciphertext: buffer, AAD: buffer?): (boolean, buffer?)
	if not Key or typeof(Key) ~= "buffer" then
		error("Key must be a buffer", 2)
	end
	if not IV or typeof(IV) ~= "buffer" then
		error("IV must be a buffer", 2)
	end
	if not Ciphertext or typeof(Ciphertext) ~= "buffer" then
		error("Ciphertext must be a buffer", 2)
	end

	local KeyLength = buffer.len(Key)
	if KeyLength ~= 16 and KeyLength ~= 24 and KeyLength ~= 32 then
		error("Key must be 16, 24, or 32 bytes", 2)
	end

	local RoundKeysBuffer = ExpandKeySchedule(Key, KeyLength, buffer.create(KEY_CONFIGS[KeyLength].ExpandedLength))
	local KeyMaterialLength = KEY_CONFIGS[KeyLength].MaterialLength

	local function EncryptionProcessor(PlaintextBlock: buffer, PlaintextOffset: number, OutputBuffer: buffer, OutputOffset: number)
		EncryptBlock(RoundKeysBuffer, KeyMaterialLength, PlaintextBlock, PlaintextOffset, OutputBuffer, OutputOffset)
	end

	local IVLen = buffer.len(IV)
	local AADLen = buffer.len(AAD or buffer.create(0))
	local CryptLen = buffer.len(Ciphertext)
	local AuthData = AAD or buffer.create(0)

	local OutputBuffer = buffer.create(CryptLen)

	local H = buffer.create(16)
	local J0 = buffer.create(16)
	local S = buffer.create(16)

	EncryptionProcessor(H, 0, H, 0)
	PrepareJ0(IV, IVLen, H, J0)
	GcmGctr(EncryptionProcessor, J0, Ciphertext, CryptLen, OutputBuffer)
	GcmHash(H, AuthData, AADLen, Ciphertext, CryptLen, S)

	return true, OutputBuffer
end

local cryptography = {
	AES = AES,
	HASHES = {
		["sha1"] = SHA1,
		["sha384"] = SHA384,
		["sha512"] = SHA512,
		["md5"] = MD5,
		["sha256"] = SHA256,
		["sha3_224"] = SHA3_224,
		["sha3_256"] = SHA3_256,
		["sha3_512"] = SHA3_512
	}
}

return cryptography