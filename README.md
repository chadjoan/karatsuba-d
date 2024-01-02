# karatsuba-d

Example implementation of branchless Karatsuba multiplication in the D programming language.

## Example Usage
```D
import karatsuba_d;

import std.format;
import std.stdio;

int main(string[] args)
{
	pragma(msg,"Compiling `karatsuba-d` usage example");
	writeln("Running `karatsuba-d` usage example");

	// Convenient version for when the result fits within built-in integers.
	ubyte  a8 = 0x80;
	ubyte  b8 = 0x7F;
	ushort r16 = mult_karatsuba(a8,b8);
	assert(0x3F80 == r16);
	writefln("The product of 0x%02X and 0x%02X is 0x%04X",
		a8, b8, r16);

	// Works at compile-time, too.
	enum ushort a16 = 0xF00F;
	enum ushort b16 = 0xB00F;
	enum uint r32 = mult_karatsuba(a16,b16);
	static assert(0XA51860E1 == r32);
	pragma(msg,format("The product of 0x%04X and 0x%04X is 0x%08X",
		a16, b16, r32));
	writefln("The product of 0x%04X and 0x%04X is 0x%08X",
		a16, b16, r32);

	// Struct-returning version for emitting larger results.
	ulong  a64 = 0xAceBe11e_CafeBabe_UL;
	ulong  b64 = 0xF100fCa7_F1edFa57_UL;
	KaratsubaInteger!ulong  r128 = mult_karatsuba_full(a64,b64);
	assert(0x8E9C_2945_7ED5_0292 == r128.lo);
	assert(0xA2CA_B997_9FFE_C71C == r128.hi);
	writefln("The product of 0x%08X and 0x%08X is 0x%08X%08X",
		a64, b64, r128.hi, r128.lo);
	writeln("");

	return 0;
}
```
## Details

This code is meant to be usable as a guide when implementing a better-optimized version, ex: in SIMD assembly or GPU shaders. It might also be useful as a quick way to implement compile-time wide integers for use in CTFE functions. As such, this is not an optimized implementation. It shows how to do Karastuba multiplication in a branchless way, and also handle all of the corner-cases (ex: overflow|carry|borrow of intermediate results).

It is intended to be (indirectly) beneficial to bespoke wide-integer (or fixed-point integer) implementations. It is not intended to help with Big Integer implementation. There are algorithms with better time-complexity for the really large integers, but for integers that are smaller (but still wider than 64 bits), the simplicity of this method might be quite helpful. Eventually, this should demonstrate multiplication for things like 96-bit, 128-bit, or 256-bit integer results. Of course, there's nothing wrong with modifying this to help with big integers, it's just that there are better options out there for that.

This version is non-recursive. Handling the recursion optimally will involve some memory management concerns, the details of which will change when rewriting this in different places (ex: SIMD or shaders).
