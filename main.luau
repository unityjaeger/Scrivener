--!native
--!optimize 2
--!strict

local RESERVED_BUFFER_SIZE = 1e6
local RESERVED_BUFFER = buffer.create(RESERVED_BUFFER_SIZE)
local PI = math.pi

export type WriteCursor = {
	pos: number,
	global_offset: number
}

export type ReadCursor = {
	pos: number,
	buff: buffer
}

export type Descriptor<T> = {
	write: (cursor: WriteCursor, value: T) -> (),
	read: (cursor: ReadCursor) -> T,
	optional: boolean?
}

export type TupleDescriptor<T...> = {
	write: (cursor: WriteCursor, T...) -> (),
	read: (cursor: ReadCursor) -> T...
}

type StructField = Descriptor<any> & {
	name: string
}

type OptStructField = StructField & {
	bitmask: number
}

type function EitherOr(a: type, b: type)
	if a:is("unknown") then
		return b
	else
		return a
	end
end

export type function SetTransformer(t: type)
	local new = types.newtable()
	for _, v in t:components() do
		new:setproperty(v, types.optional(types.boolean))
	end
	return Descriptor(new :: any)
end

type function GetDescriptorType(t: type)
	if t.tag ~= "table" then
		return types.never
	end

	local des_fn = t:readproperty(types.singleton("read"))
	if not des_fn or not des_fn:is("function") then
		return types.never
	end

	local ret = des_fn:returns().head
	if not ret or not ret[1] then
		return types.never
	end

	return ret[1]
end

type function StructTransformer(t: type)
	if t.tag ~= "table" then
		return t
	end

	local mt = t:metatable()
	if mt then
		local index_singleton = types.singleton("__index")
		for key, v in mt:properties() do
			if key == index_singleton then
				t = v.read or v.write :: any
			end
		end
	end

	local tbl_props = t:properties()

	local phantom_data = GetDescriptorType(t)
	if phantom_data ~= types.never then
		return StructTransformer(phantom_data)
	end

	local indexer = t:indexer()
	if indexer then
		local new = types.newtable()
		new:setindexer(StructTransformer(indexer.index), StructTransformer(indexer.readresult))
		return new :: any
	end

	local new = types.newtable()
	for key, v in tbl_props do
		local value = v.read or v.write
		new:setproperty(key, StructTransformer(value))
	end
	return new :: any
end

type function VariantTransformer(t: type)
	local t_props = t:properties()

	local intersect

	for k, v in t_props do
		local new_t = types.newtable()
		new_t:setproperty(types.singleton("kind"), k)
		new_t:setproperty(types.singleton("value"), StructTransformer(v.read))

		if not intersect then
			intersect = new_t
		else
			intersect = types.unionof(intersect, new_t)
		end
	end

	return intersect :: any
end

local function writei24_helper(buff: buffer, offset: number, value: number): ()
	if value < 0 then
		value = value + 16777216
	end
	buffer.writeu16(buff, offset, value / 256)
	buffer.writeu8(buff, offset + 2, value)
end

local function readi24_helper(buff: buffer, offset: number): number
	local value = 256 * buffer.readu16(buff, offset) + buffer.readu8(buff, offset + 2)
	if value >= 8388608 then
		return value - 16777216
	end
	return value
end

local function writeu24_helper(buff: buffer, offset: number, value: number): ()
	buffer.writeu16(buff, offset, value / 256)
	buffer.writeu8(buff, offset + 2, value)
end

local function readu24_helper(buff: buffer, offset: number): number
	return 256 * buffer.readu16(buff, offset) + buffer.readu8(buff, offset + 2)
end

local function writeu53_helper(buff: buffer, offset: number, value: number): ()
	buffer.writeu32(buff, offset, value / 16777216)
	writeu24_helper(buff, offset + 4, value)
end

local function readu53_helper(buff: buffer, offset: number): number
	return 16777216 * buffer.readu32(buff, offset) + readu24_helper(buff, offset + 4)
end

local function writei53_helper(buff: buffer, offset: number, value: number): ()
	if value < 0 then
		value = value + 9007199254740992
	end
	buffer.writeu32(buff, offset, value / 16777216)
	writeu24_helper(buff, offset + 4, value)
end

local function readi53_helper(buff: buffer, offset: number): number
	local value = 16777216 * buffer.readu32(buff, offset) + readu24_helper(buff, offset + 4)
	if value >= 4503599627370496 then
		value = value - 9007199254740992
	end
	return value
end

local function writef16_helper(buff: buffer, offset: number, value: number): ()
	if value ~= value then
		buffer.writeu16(buff, offset, 0x7E01)
		return
	elseif value == 0 then
		buffer.writeu16(buff, offset, 0x0000)
		return
	end

	local sign = 0
	if value < 0 then
		sign = 0x8000
		value = -value
	end

	if value > 65504 then
		buffer.writeu16(buff, offset, bit32.bor(sign, 0x7C00))
		return
	end

	local fraction, exponent = math.frexp(value)
	if exponent < -13 then
		fraction = fraction * math.ldexp(1, exponent + 13)
		exponent = 0
	else
		exponent = exponent + 14
		fraction = (fraction * 2 - 1)
	end

	buffer.writeu16(buff, offset, bit32.bor(
		sign,
		bit32.lshift(exponent, 10),
		fraction * 1024
	))
end

local function readf16_helper(buff: buffer, offset: number): number
	local value = buffer.readu16(buff, offset)

	local banded = bit32.band(value, 0x7C00)
	if value == 0 then
		return (bit32.band(value, 0x8000) ~= 0) and -0 or 0
	elseif value == 0x7C00 then
		return math.huge
	elseif value == 0xFC00 then
		return -math.huge
	elseif (banded == 0x7C00) and (bit32.band(value, 0x03FF) ~= 0) then
		return 0/0
	end

	local sign = bit32.band(value, 0x8000) == 0 and 1 or -1
	local exponent = bit32.rshift(banded, 10)
	local fraction = bit32.band(value, 0x03FF) / 1024

	if exponent == 0 then
		return sign * math.ldexp(fraction, -14)
	else
		return sign * math.ldexp(1 + fraction, exponent - 15)
	end
end

local function inverse_table<T>(tbl: {T}): {[T]: number}
	local inverse = {}
	for i, v in tbl do
		inverse[v] = i
	end
	return inverse
end

local function write_cursor(global_offset: number?): WriteCursor
	return {
		pos = global_offset or 0,
		global_offset = global_offset or 0
	}
end

local function finalize(cursor: WriteCursor): buffer
	local global_offset, pos = cursor.global_offset, cursor.pos
	local buff = buffer.create(pos)
	local count = pos - global_offset
	buffer.copy(buff, 0, RESERVED_BUFFER, global_offset, count)
	cursor.pos = global_offset
	return buff
end

local function read_cursor(buff: buffer): ReadCursor
	local buffer_len = buffer.len(buff)
	if buffer_len > RESERVED_BUFFER_SIZE then
		error(string.format("input buffer size exceeds maximum size %d, got %d", RESERVED_BUFFER_SIZE, buffer_len))
	end

	return {
		pos = 0,
		buff = buff
	}
end

local function writeu8(cursor: WriteCursor, value: number)
	buffer.writeu8(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 1
end

local function writeu16(cursor: WriteCursor, value: number)
	buffer.writeu16(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 2
end

local function writeu24(cursor: WriteCursor, value: number)
	writeu24_helper(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 3
end

local function writeu32(cursor: WriteCursor, value: number)
	buffer.writeu32(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 4
end

local function writeu53(cursor: WriteCursor, value: number)
	writeu53_helper(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 7
end

local function readu8(cursor: ReadCursor): number
	local value = buffer.readu8(cursor.buff, cursor.pos)
	cursor.pos += 1
	return value
end

local function readu16(cursor: ReadCursor): number
	local value = buffer.readu16(cursor.buff, cursor.pos)
	cursor.pos += 2
	return value
end

local function readu24(cursor: ReadCursor): number
	local value = readu24_helper(cursor.buff, cursor.pos)
	cursor.pos += 3
	return value
end

local function readu32(cursor: ReadCursor): number
	local value = buffer.readu32(cursor.buff, cursor.pos)
	cursor.pos += 4
	return value
end

local function readu53(cursor: ReadCursor): number
	local value = readu53_helper(cursor.buff, cursor.pos)
	cursor.pos += 7
	return value
end

local function writei8(cursor: WriteCursor, value: number)
	buffer.writei8(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 1
end

local function writei16(cursor: WriteCursor, value: number)
	buffer.writei16(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 2
end

local function writei24(cursor: WriteCursor, value: number)
	writei24_helper(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 3
end

local function writei32(cursor: WriteCursor, value: number)
	buffer.writei32(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 4
end

local function writei53(cursor: WriteCursor, value: number)
	writei53_helper(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 7
end

local function readi8(cursor: ReadCursor): number
	local value = buffer.readi8(cursor.buff, cursor.pos)
	cursor.pos += 1
	return value
end

local function readi16(cursor: ReadCursor): number
	local value = buffer.readi16(cursor.buff, cursor.pos)
	cursor.pos += 2
	return value
end

local function readi24(cursor: ReadCursor): number
	local value = readi24_helper(cursor.buff, cursor.pos)
	cursor.pos += 3
	return value
end

local function readi32(cursor: ReadCursor): number
	local value = buffer.readi32(cursor.buff, cursor.pos)
	cursor.pos += 4
	return value
end

local function readi53(cursor: ReadCursor): number
	local value = readi53_helper(cursor.buff, cursor.pos)
	cursor.pos += 7
	return value
end

local function writef16(cursor: WriteCursor, value: number)
	writef16_helper(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 2
end

local function writef32(cursor: WriteCursor, value: number)
	buffer.writef32(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 4
end

local function writef64(cursor: WriteCursor, value: number)
	buffer.writef64(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += 8
end

local function readf16(cursor: ReadCursor): number
	local value = readf16_helper(cursor.buff, cursor.pos)
	cursor.pos += 2
	return value
end

local function readf32(cursor: ReadCursor): number
	local value = buffer.readf32(cursor.buff, cursor.pos)
	cursor.pos += 4
	return value
end

local function readf64(cursor: ReadCursor): number
	local value = buffer.readf64(cursor.buff, cursor.pos)
	cursor.pos += 8
	return value
end

local function writevlq(cursor: WriteCursor, value: number)
	repeat
		local byte = value % 2^7
		value = (value - byte) / 2^7

		if value > 0 then
			byte += 2^7
		end

		writeu8(cursor, byte)
	until value == 0
end

local function readvlq(cursor: ReadCursor): number
	local result = 0
	local shift = 1

	repeat
		local byte = readu8(cursor)
		local chunk = byte % 2^7

		result += chunk * shift
		shift *= 2^7
	until byte < 2^7

	return result
end

local function writesvlq(cursor: WriteCursor, value: number)
	if value >= 0 then
		writevlq(cursor, value * 2)
	else
		writevlq(cursor, -value * 2 - 1)
	end
end

local function readsvlq(cursor: ReadCursor): number
	local value = readvlq(cursor)

	if value % 2 == 0 then
		return value / 2
	else
		return -(value + 1) / 2
	end
end

local function writebuffer(cursor: WriteCursor, value: buffer)
	local len = buffer.len(value)
	writevlq(cursor, len)
	buffer.copy(RESERVED_BUFFER, cursor.pos, value, 0)
	cursor.pos += len
end

local function readbuffer(cursor: ReadCursor): buffer
	local len = readvlq(cursor)
	local result = buffer.create(len)
	buffer.copy(result, 0, cursor.buff, cursor.pos, len)
	cursor.pos += len
	return result
end

local function writebool(cursor: WriteCursor, a: boolean, b: boolean?, c: boolean?, d: boolean?, e: boolean?, f: boolean?, g: boolean?, h: boolean?)
	writeu8(cursor,
		(a and 2^0 or 0) +
		(b and 2^1 or 0) +
		(c and 2^2 or 0) +
		(d and 2^3 or 0) +
		(e and 2^4 or 0) +
		(f and 2^5 or 0) +
		(g and 2^6 or 0) +
		(h and 2^7 or 0)
	)
end

local function readbool(cursor: ReadCursor): (boolean, boolean, boolean, boolean, boolean, boolean, boolean, boolean)
	local value = readu8(cursor)
	return
		bit32.band(value, 2^0) ~= 0,
		bit32.band(value, 2^1) ~= 0,
		bit32.band(value, 2^2) ~= 0,
		bit32.band(value, 2^3) ~= 0,
		bit32.band(value, 2^4) ~= 0,
		bit32.band(value, 2^5) ~= 0,
		bit32.band(value, 2^6) ~= 0,
		bit32.band(value, 2^7) ~= 0
end

local function writebool_simple(cursor: WriteCursor, value: boolean)
	writeu8(cursor, value and 1 or 0)
end

local function readboool_simple(cursor: ReadCursor): boolean
	return readu8(cursor) == 1
end

local function writestring(cursor: WriteCursor, value: string)
	local len = string.len(value)
	writevlq(cursor, len)
	buffer.writestring(RESERVED_BUFFER, cursor.pos, value)
	cursor.pos += len
end

local function readstring(cursor: ReadCursor): string
	local len = readvlq(cursor)
	local value = buffer.readstring(cursor.buff, cursor.pos, len)
	cursor.pos += len
	return value
end

local function writecolor3(cursor: WriteCursor, value: Color3)
	writeu8(cursor, value.R * 255)
	writeu8(cursor, value.G * 255)
	writeu8(cursor, value.B * 255)
end

local function readcolor3(cursor: ReadCursor): Color3
	return Color3.fromRGB(
		readu8(cursor),
		readu8(cursor),
		readu8(cursor)
	)
end

local function writeopt<T>(cursor: WriteCursor, write_method: (cursor: WriteCursor, value: T) -> (), value: T?)
	if value == nil then
		writeu8(cursor, 0)
	else
		writeu8(cursor, 1)
		write_method(cursor, value)
	end
end

local function readopt<T>(cursor: ReadCursor, read_method: (cursor: ReadCursor) -> T): T?
	local present = readu8(cursor)
	if present == 1 then
		return read_method(cursor)
	else
		return nil
	end
end

local function mark_opt<T>(inner: Descriptor<T>): Descriptor<T?>
	local copy = table.clone(inner)
	copy.optional = true
	return copy
end

local u8_descriptor: Descriptor<number> = {
	write = writeu8,
	read = readu8,
}

local u16_descriptor: Descriptor<number> = {
	write = writeu16,
	read = readu16,
}

local u24_descriptor: Descriptor<number> = {
	write = writeu24,
	read = readu24,
}

local u32_descriptor: Descriptor<number> = {
	write = writeu32,
	read = readu32,
}

local u53_descriptor: Descriptor<number> = {
	write = writeu53,
	read = readu53,
}

local i8_descriptor: Descriptor<number> = {
	write = writei8,
	read = readi8,
}

local i16_descriptor: Descriptor<number> = {
	write = writei16,
	read = readi16,
}

local i24_descriptor: Descriptor<number> = {
	write = writei24,
	read = readi24,
}

local i32_descriptor: Descriptor<number> = {
	write = writei32,
	read = readi32,
}

local i53_descriptor: Descriptor<number> = {
	write = writei53,
	read = readi53,
}

local f16_descriptor: Descriptor<number> = {
	write = writef16,
	read = readf16,
}

local f32_descriptor: Descriptor<number> = {
	write = writef32,
	read = readf32,
}

local f64_descriptor: Descriptor<number> = {
	write = writef64,
	read = readf64,
}

local vlq_descriptor: Descriptor<number> = {
	write = writevlq,
	read = readvlq,
}

local svlq_descriptor: Descriptor<number> = {
	write = writesvlq,
	read = readsvlq
}

local buffer_descriptor: Descriptor<buffer> = {
	write = writebuffer,
	read = readbuffer
}

local string_descriptor: Descriptor<string> = {
	write = writestring,
	read = readstring,
}

local bool_descriptor: TupleDescriptor<...boolean> = {
	write = writebool,
	read = readbool
}

local bool_simple_descriptor: Descriptor<boolean> = {
	write = writebool_simple,
	read = readboool_simple
}

local color3_descriptor: Descriptor<Color3> = {
	write = writecolor3,
	read = readcolor3
}

local literal_descriptor_cache = {}
local function literal_descriptor<T>(literals: {T}): Descriptor<T>
	if literal_descriptor_cache[literals] then
		return literal_descriptor_cache[literals]
	end

	if #literals > 255 then
		error(string.format("cannot have more than 255 literals, got %d", #literals))
	end

	local inverse_literals = inverse_table(literals)

	local descriptor: Descriptor<T> = {
		write = function(cursor, value: T)
			local index = inverse_literals[value]
			writeu8(cursor, index - 1)
		end,
		read = function(cursor)
			local index = readu8(cursor)
			return literals[index + 1]
		end,
	}

	literal_descriptor_cache[literals] = descriptor

	return descriptor
end

local vector_descriptor_cache = {}
local function vector3_descriptor(number_descriptor: Descriptor<number>): Descriptor<Vector3>
	if vector_descriptor_cache[number_descriptor] then
		return vector_descriptor_cache[number_descriptor]
	end

	local write, read = number_descriptor.write, number_descriptor.read

	local descriptor: Descriptor<Vector3> = {
		write = function(cursor, value: Vector3)
			write(cursor, value.X)
			write(cursor, value.Y)
			write(cursor, value.Z)
		end,
		read = function(cursor)
			return Vector3.new(
				read(cursor),
				read(cursor),
				read(cursor)
			)
		end,
	}

	vector_descriptor_cache[number_descriptor] = descriptor

	return descriptor
end

local opt_descriptor_cache = {}
local function opt_descriptor<T>(inner: Descriptor<T>): Descriptor<T?>
	if opt_descriptor_cache[inner] then
		return opt_descriptor_cache[inner]
	end

	local write, read = inner.write, inner.read

	--inline for slightly better speed yknow
	local descriptor: Descriptor<T?> = {
		write = function(cursor, value: T?)
			if value == nil then
				writeu8(cursor, 0)
			else
				writeu8(cursor, 1)
				write(cursor, value)
			end
		end,
		read = function(cursor)
			local present = readu8(cursor)
			if present == 1 then
				return read(cursor)
			else
				return nil
			end
		end,
	}

	opt_descriptor_cache[inner] = descriptor

	return descriptor
end

local function simple_struct<T>(fields: {StructField}): Descriptor<T>
	return {
		write = function(cursor, value)
			for _, inner in fields do
				inner.write(cursor, value[inner.name])
			end
		end,
		read = function(cursor)
			local result = {}
			for _, inner in fields do
				result[inner.name] = inner.read(cursor)
			end
			return result
		end,
	}
end

local function optional_struct<T>(fields: {StructField}, opt_fields: {OptStructField}, byte_descriptor: Descriptor<number>): Descriptor<T>
	local write_byte, read_byte = byte_descriptor.write, byte_descriptor.read

	return {
		write = function(cursor, value)
			local byte = 0
			for _, inner in opt_fields do
				local field_value = value[inner.name]
				if field_value ~= nil then
					byte = bit32.bor(byte, inner.bitmask)
				end
			end

			write_byte(cursor, byte)

			for _, inner in opt_fields do
				local field_value = value[inner.name]
				if field_value ~= nil then
					inner.write(cursor, field_value)
				end
			end

			for _, inner in fields do
				inner.write(cursor, value[inner.name])
			end
		end,
		read = function(cursor)
			local result = {}
			local byte = read_byte(cursor)

			for _, inner in opt_fields do
				if bit32.band(byte, inner.bitmask) ~= 0 then
					result[inner.name] = inner.read(cursor)
				end
			end

			for _, inner in fields do
				result[inner.name] = inner.read(cursor)
			end

			return result
		end,
	}
end

local struct_descriptor_cache = {}
local function struct_descriptor_hidden<T>(struct: T): Descriptor<T>
	if struct_descriptor_cache[struct] then
		return struct_descriptor_cache[struct]
	end

	local fields: {StructField} = {}
	local opt_fields: {OptStructField} = {}
	local opt_count = 0	

	for name, inner in struct :: {[string]: Descriptor<any>} do
		if inner.optional then
			table.insert(opt_fields, {
				name = name,
				write = inner.write,
				read = inner.read,
				bitmask = bit32.lshift(1, opt_count)
			} :: OptStructField)

			opt_count += 1
			
			if opt_count > 32 then
				error(string.format("structs can not have more than 32 optional fields, got %d", opt_count))
			end
		else
			table.insert(fields, {
				name = name,
				write = inner.write,
				read = inner.read
			} :: StructField)
		end
	end

	table.sort(opt_fields, function(a: OptStructField, b: OptStructField) return a.name < b.name end)
	table.sort(fields, function(a: StructField, b: StructField) return a.name < b.name end)

	local byte_descriptor: Descriptor<number>
	if opt_count <= 8 then
		byte_descriptor = u8_descriptor
	elseif opt_count <= 16 then
		byte_descriptor = u16_descriptor
	elseif opt_count <= 24 then
		byte_descriptor = u24_descriptor
	else
		byte_descriptor = u32_descriptor
	end

	local descriptor: Descriptor<T>
	if opt_count == 0 then
		descriptor = simple_struct(fields)
	else
		descriptor = optional_struct(fields, opt_fields, byte_descriptor)
	end

	struct_descriptor_cache[struct] = descriptor

	return descriptor
end

local function struct_descriptor<T>(struct: T): Descriptor<StructTransformer<T>>
	return struct_descriptor_hidden(struct)
end

local array_descriptor_cache = {}
local function array_descriptor<T>(element_descriptor: Descriptor<T>): Descriptor<{T}>
	if array_descriptor_cache[element_descriptor] then
		return array_descriptor_cache[element_descriptor]
	end

	local write, read = element_descriptor.write, element_descriptor.read

	local descriptor: Descriptor<{T}> = {
		write = function(cursor, value: {T})
			writevlq(cursor, #value)
			for _, entry in value do
				write(cursor, entry)
			end
		end,
		read = function(cursor)
			local len = readvlq(cursor)
			local result = table.create(len)
			for i = 1, len do
				table.insert(result, read(cursor))
			end
			return result
		end,
	}

	array_descriptor_cache[element_descriptor] = descriptor

	return descriptor
end

local map_descriptor_cache = {}
local function map_descriptor<K, V>(key_descriptor: Descriptor<K>, value_descriptor: Descriptor<V>): Descriptor<{[K]: V}>
	if map_descriptor_cache[key_descriptor] and map_descriptor_cache[key_descriptor][value_descriptor] then
		return map_descriptor_cache[key_descriptor][value_descriptor]
	end

	local key_write, key_read = key_descriptor.write, key_descriptor.read
	local value_write, value_read = value_descriptor.write, value_descriptor.read

	local descriptor: Descriptor<{[K]: V}> = {
		write = function(cursor, value: {[K]: V})
			local len = 0
			for key, entry in value do
				len += 1
			end

			writevlq(cursor, len)

			for key, entry in value do
				key_write(cursor, key)
				value_write(cursor, entry)
			end
		end,
		read = function(cursor)
			local len = readvlq(cursor)
			local map = {}

			for i = 1, len do
				map[key_read(cursor)] = value_read(cursor)
			end

			return map
		end,
	}

	map_descriptor_cache[key_descriptor] = {[value_descriptor] = descriptor}

	return descriptor
end

local id_to_rotation = {
	CFrame.Angles(0, 0, 0),
	CFrame.Angles(math.rad(90), 0, 0),
	CFrame.Angles(0, math.rad(180), math.rad(180)),
	CFrame.Angles(math.rad(-90), 0, 0),
	CFrame.Angles(0, math.rad(180), math.rad(90)),
	CFrame.Angles(0, math.rad(90), math.rad(90)),
	CFrame.Angles(0, 0, math.rad(90)),
	CFrame.Angles(0, math.rad(-90), math.rad(90)),
	CFrame.Angles(math.rad(-90), math.rad(-90), 0),
	CFrame.Angles(0, math.rad(-90), 0),
	CFrame.Angles(math.rad(90), math.rad(-90), 0),
	CFrame.Angles(0, math.rad(90), math.rad(180)),
	CFrame.Angles(0, math.rad(-90), math.rad(180)),
	CFrame.Angles(0, math.rad(180), 0),
	CFrame.Angles(math.rad(-90), math.rad(-180), 0),
	CFrame.Angles(0, 0, math.rad(180)),
	CFrame.Angles(math.rad(90), math.rad(180), 0),
	CFrame.Angles(0, 0, math.rad(-90)),
	CFrame.Angles(0, math.rad(-90), math.rad(-90)),
	CFrame.Angles(0, math.rad(-180), math.rad(-90)),
	CFrame.Angles(0, math.rad(90), math.rad(-90)),
	CFrame.Angles(math.rad(90), math.rad(90), 0),
	CFrame.Angles(0, math.rad(90), 0),
	CFrame.Angles(math.rad(-90), math.rad(90), 0),
}

local rotation_to_id: {[number]: {[number]: {[number]: number}}} = {}
do
	for id, cframe in id_to_rotation do
		local x, y, z = cframe:ToOrientation()

		rotation_to_id[x] = rotation_to_id[x] or {}
		rotation_to_id[x][y] = rotation_to_id[x][y] or {}
		rotation_to_id[x][y][z] = id
	end
end

local cframe_descriptor_cache = {}
local function cframe_descriptor(position_descriptor: Descriptor<number>, position_scale: number?): Descriptor<CFrame>
	if cframe_descriptor_cache[position_descriptor] then
		warn("cached cframe descriptors may not have the same position_scale if a different position_scale was defined")
		return cframe_descriptor_cache[position_descriptor]
	end

	local position_write, position_read = position_descriptor.write, position_descriptor.read

	local scale = position_scale or 1

	local descriptor: Descriptor<CFrame> = {
		write = function(cursor, value: CFrame)
			local rot_x, rot_y, rot_z = value:ToOrientation()
			local id = rotation_to_id[rot_x] and rotation_to_id[rot_x][rot_y] and rotation_to_id[rot_x][rot_y][rot_z]
			if id then
				writeu8(cursor, id)
			else
				writeu8(cursor, 0)
				writeu16(cursor, math.map(rot_x, -PI, PI, 0, 2^16 - 1))
				writeu16(cursor, math.map(rot_y, -PI, PI, 0, 2^16 - 1))
				writeu16(cursor, math.map(rot_z, -PI, PI, 0, 2^16 - 1))
			end

			position_write(cursor, value.X * scale)
			position_write(cursor, value.Y * scale)
			position_write(cursor, value.Z * scale)
		end,
		read = function(cursor)
			local id = readu8(cursor)
			local angles = id_to_rotation[id]
			if angles then
				return CFrame.new(
					position_read(cursor) / scale,
					position_read(cursor) / scale,
					position_read(cursor) / scale
				) * angles
			else
				local q_x = math.map(readu16(cursor), 0, 2^16 - 1, -PI, PI)
				local q_y = math.map(readu16(cursor), 0, 2^16 - 1, -PI, PI)
				local q_z = math.map(readu16(cursor), 0, 2^16 - 1, -PI, PI)
				local w = math.sqrt(1 - math.clamp(q_x * q_x + q_y * q_y + q_z * q_z, 0, 1))

				return CFrame.new(
					position_read(cursor) / scale,
					position_read(cursor) / scale,
					position_read(cursor) / scale,
					q_x, q_y, q_z, w
				)
			end
		end,
	}

	cframe_descriptor_cache[position_descriptor] = descriptor

	return descriptor
end

local variant_descriptor_cache = {}
local function variant_descriptor_hidden<T>(variants: T): Descriptor<T>
	if variant_descriptor_cache then
		return variant_descriptor_cache[variants]
	end

	local literals: {string} = {}
	for kind in variants :: {[string]: Descriptor<any>} do
		table.insert(literals, kind)
	end

	local kind_descriptor = literal_descriptor(literals)
	local kind_write, kind_read = kind_descriptor.write, kind_descriptor.read

	local descriptor: Descriptor<{ kind: string, value: any }> = {
		write = function(cursor, value)
			local kind = value.kind
			local payload = value.value

			local inner = (variants :: {[string]: Descriptor<any>})[kind]
			kind_write(cursor, kind)
			inner.write(cursor, payload)
		end,

		read = function(cursor)
			local kind = kind_read(cursor)
			local inner = (variants :: {[string]: Descriptor<any>})[kind]
			local payload = inner.read(cursor)

			return {
				kind = kind,
				value = payload,
			}
		end
	}

	variant_descriptor_cache[variants] = descriptor

	return descriptor
end

local function variant_descriptor<T>(variants: T): Descriptor<VariantTransformer<T>>
	return variant_descriptor_hidden(variants)
end

local bitarray_descriptor_cache = {}
local function bitarray_descriptor(byte_count: number): Descriptor<{boolean}>
	if bitarray_descriptor_cache[byte_count] then
		return bitarray_descriptor_cache[byte_count]
	end

	local descriptor: Descriptor<{boolean}> = {
		write = function(cursor, value: {boolean})
			for i = 0, byte_count - 1 do
				local j = i * 8
				writebool(cursor, value[j + 1], value[j + 2], value[j + 3], value[j + 4], value[j + 5], value[j + 6], value[j + 7], value[j + 8])
			end
		end,
		read = function(cursor)
			local result = table.create(byte_count * 8, false) :: {boolean}
			for i = 0, byte_count - 1 do
				local j = i * 8
				result[j + 1], result[j + 2], result[j + 3], result[j + 4], result[j + 5], result[j + 6], result[j + 7], result[j + 8] = readbool(cursor)
			end
			return result
		end,
	}

	bitarray_descriptor_cache[byte_count] = descriptor

	return descriptor
end

local set_descriptor_cache = {}
local function set_descriptor<T>(set: {string}): Descriptor<EitherOr<T, {[string]: boolean?}>>
	if set_descriptor_cache[set] then
		return set_descriptor_cache[set]
	end

	local name_to_index = {}
	for i, name in set :: {string} do
		name_to_index[name] = i
	end

	local len = #set
	local bitarray = bitarray_descriptor(math.ceil(len / 8))
	local bitarray_write, bitarray_read = bitarray.write, bitarray.read

	local descriptor: Descriptor<T> = {
		write = function(cursor, value: {[string]: boolean?})
			local bools = table.create(len, false)

			for name, bool in value do
				if bool == true then
					bools[name_to_index[name]] = true
				end
			end

			bitarray_write(cursor, bools :: {boolean})
		end,
		read = function(cursor)
			local bools = bitarray_read(cursor)
			local result = {}

			for i, name in set :: {string} do
				if bools[i] == true then
					result[name] = true
				end
			end

			return result
		end,
	}

	set_descriptor_cache[set] = descriptor

	return descriptor
end

local function get_reserved_buffer(): buffer
	return RESERVED_BUFFER
end

return {
	write_cursor = write_cursor,
	read_cursor = read_cursor,
	finalize = finalize,

	writeu8 = writeu8,
	writeu16 = writeu16,
	writeu24 = writeu24,
	writeu32 = writeu32,
	writeu53 = writeu53,
	readu8 = readu8,
	readu16 = readu16,
	readu24 = readu24,
	readu32 = readu32,
	readu53 = readu53,

	writei8 = writei8,
	writei16 = writei16,
	writei24 = writei24,
	writei32 = writei32,
	writei53 = writei53,
	readi8 = readi8,
	readi16 = readi16,
	readi24 = readi24,
	readi32 = readi32,
	readi53 = readi53,

	writef16 = writef16,
	writef32 = writef32,
	writef64 = writef64,
	readf16 = readf16,
	readf32 = readf32,
	readf64 = readf64,

	writevlq = writevlq,
	readvlq = readvlq,

	writebuffer = writebuffer,
	readbuffer = readbuffer,

	writebool = writebool,
	readbool = readbool,

	writestring = writestring,
	readstring = readstring,

	writecolor3 = writecolor3,
	readcolor3 = readcolor3,

	writeopt = writeopt,
	readopt = readopt,
	mark_opt = mark_opt,

	u8 = u8_descriptor,
	u16 = u16_descriptor,
	u24 = u24_descriptor,
	u32 = u32_descriptor,
	u53 = u53_descriptor,

	i8 = i8_descriptor,
	i16 = i16_descriptor,
	i24 = i24_descriptor,
	i32 = i32_descriptor,
	i53 = i53_descriptor,

	f16 = f16_descriptor,
	f32 = f32_descriptor,
	f64 = f64_descriptor,

	vlq = vlq_descriptor,
	svlq = svlq_descriptor,

	buffer = buffer_descriptor,

	bool = bool_descriptor,
	bool_simple = bool_simple_descriptor,

	string = string_descriptor,

	color3 = color3_descriptor,

	literal = literal_descriptor,
	vector3 = vector3_descriptor,
	opt = opt_descriptor,
	struct = struct_descriptor,
	array = array_descriptor,
	map = map_descriptor,
	cframe = cframe_descriptor,
	variant = variant_descriptor,
	bitarray = bitarray_descriptor,
	set = set_descriptor,

	get_reserved_buffer = get_reserved_buffer
}