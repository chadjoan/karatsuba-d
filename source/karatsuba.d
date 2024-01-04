module karatsuba_d;

import std.traits : isIntegral, isUnsigned;

struct KaratsubaInteger(ComponentInteger)
	if (isIntegral!ComponentInteger && isUnsigned!ComponentInteger)
{
	ComponentInteger  lo;
	ComponentInteger  hi;
}

template KaratsubaInteger(ushort n_bits_total)
{
	import std.format;
	static if (n_bits_total <= 16) // 16 bits is representable by two ubytes.
		alias KaratsubaInteger = KaratsubaInteger!ubyte;
	else
	static if (n_bits_total <= 32) // 32 bits is representable by two ushorts.
		alias KaratsubaInteger = KaratsubaInteger!ushort;
	else
	static if (n_bits_total <= 64) // 64 bits is representable by two uints.
		alias KaratsubaInteger = KaratsubaInteger!uint;
	else
	static if (n_bits_total <= 128) // 128 bits is representable by two ulongs.
		alias KaratsubaInteger = KaratsubaInteger!ulong;
	else
		static assert(0, format("%d-bit wide KaratsubaInteger struct is not implemented, sorry.",n_bits_total));
}

debug
{
	import std.stdio;

	nothrow @nogc @safe:
	// `debug_printing()` is a property to make it possible for non-debug
	// code to compile its setter as a do-nothing function (and without
	// allocating space for a boolean that is unnecessary in non-debug code).
	static bool _debug_printing = false;
	@property bool debug_printing() { return _debug_printing; }
	@property bool debug_printing(bool v) { return _debug_printing = v; }

	void kmwriteln(string ln)() {
		debug {
			if ( !__ctfe && debug_printing )
				writeln(ln);
		}
	}

	void kmwritefln(string fmtstr, A...)(A args)
	{
		debug {
			if ( !__ctfe && debug_printing )
				writefln(fmtstr, args);
		}
	}
}
else
{
	pure nothrow @nogc @safe:
	pragma(inline,true) @property bool debug_printing() { return false; }
	pragma(inline,true) @property bool debug_printing(bool v) { return false; }

	template kmwriteln(string ln) {}

	pragma(inline,true)
	void kmwritefln(string fmtstr, A...)(A args) {}
}



pure nothrow @nogc @safe
KaratsubaInteger!T  mult_karatsuba_full_pos(T)(T lhs, T rhs)
	if ( isIntegral!T && isUnsigned!T )
{
	kmwritefln!("Debugging `mult_karatsuba_full(lhs:%04X, rhs:%04X)`")(lhs, rhs);

	enum T one = cast(T)1;
	enum T n_bits = T.sizeof * 8;
	enum T lo_mask = (one << (n_bits/2)) - 1; // Ex: If (T==ushort) then (lo_mask=0x00FF);

	kmwriteln!("");
	kmwritefln!("typeof(T) == %s")(T.stringof);
	kmwritefln!("n_bits  == %d")  (n_bits);
	kmwritefln!("lo_mask == %04X")(lo_mask);

	T lhs_lo = cast(T)(lhs & lo_mask);
	T lhs_hi = cast(T)(lhs >>> (n_bits/2));
	T rhs_lo = cast(T)(rhs & lo_mask);
	T rhs_hi = cast(T)(rhs >>> (n_bits/2));

	T lhs_sum = cast(T)(lhs_lo + lhs_hi);
	T rhs_sum = cast(T)(rhs_lo + rhs_hi);
	kmwriteln!("");
	kmwritefln!("lhs_sum == %04X")(lhs_sum);
	kmwritefln!("rhs_sum == %04X")(rhs_sum);

	// Gather least-significant bits (lsb's).
	// This will be important for multiplying the middle-term factors later on.
	T lhs_lsb = lhs_sum & 1;
	T rhs_lsb = rhs_sum & 1;

	// Now that the lsb's are safe, shift these numbers down by 1 bit so
	// that they fit in (n_bits/2) bits, which then allows them to be
	// multiplied together without overflow.
	lhs_sum >>>= 1;
	rhs_sum >>>= 1;
	kmwriteln!("");
	kmwritefln!("lhs_sum == %04X")(lhs_sum);
	kmwritefln!("rhs_sum == %04X")(rhs_sum);
	kmwritefln!("lhs_lo  == %04X")(lhs_lo);
	kmwritefln!("lhs_hi  == %04X")(lhs_hi);
	kmwritefln!("rhs_lo  == %04X")(rhs_lo);
	kmwritefln!("rhs_hi  == %04X")(rhs_hi);
	kmwriteln!("");

	// We quickly run into a snag:
	// `lhs_sum` and `rhs_sum` each occupy ((n_bits/2)+1) bits, which means that
	// if we multiply them together, we'll end up with possibly (n_bits+2) bits
	// of result, which is no good becuase we can't store it in type T that
	// only has (n_bits) of bits.
	
	// So what we do below is perform that wide multiplication as _another_
	// emulated multiplication. For this sub-multiply, we use long multiplication
	// instead of Karatsuba, because it has fewer terms to compute, and because
	// most of our "multiplication" can be done with simple logical operators.
	// That's because we'll split our operands up into a lower single bit,
	// and the upper factors will be the full (n_bits)-wide T-type.
	//
	// The terms involving multiplications by single bits can instead be done
	// with simpler logical operations, and do not require a true multiply op.
	//
	// The high multiplication is just one of the 3 required multiplications
	// for the Karatsuba method to work.

	// "Multiply" the least-sig-bits:
	T qq0 = lhs_lsb & rhs_lsb;

	// "Multiply" lsb's by their counterparts, then add.
	enum T firestop_bit = (one << (n_bits/2)); // Stop carry propagation just past the first mask bit.
	enum T _ffffffff = cast(T)(-(one));
	enum T premask = _ffffffff ^ firestop_bit;

	kmwritefln!("firestp == %04X")(firestop_bit);
	kmwritefln!("fffffff == %04X")(_ffffffff);
	kmwritefln!("premask == %04X")(premask);
	kmwriteln!("");

	T lhs_mask = cast(T) ~(premask + rhs_lsb);
	T rhs_mask = cast(T) ~(premask + lhs_lsb);

	// If we wanted perfect masks, we would need to mask out the firestop bit
	// in ONLY the (lsb==0) case, because the mask will look something like
	// 0x0200 for n_bits==16.
	// But because the largest value from either sum is ((n_bits/2)+1), we can
	// safely ignore the extraneous mask bit. It won't do anything.

	T lhs_qq1 = lhs_sum & lhs_mask;
	T rhs_qq1 = rhs_sum & rhs_mask;

	T qq1 = cast(T)(lhs_qq1 + rhs_qq1);

	T q0  = cast(T)(lhs_lo  * rhs_lo );
	T qq2 = cast(T)(lhs_sum * rhs_sum);
	T q2  = cast(T)(lhs_hi  * rhs_hi );

	kmwritefln!("lhs_lsb == %04X")(lhs_lsb);
	kmwritefln!("rhs_lsb == %04X")(rhs_lsb);
	kmwritefln!("lhsmask == %04X")(lhs_mask);
	kmwritefln!("rhsmask == %04X")(rhs_mask);
	kmwritefln!("lhs_qq1 == %04X")(lhs_qq1);
	kmwritefln!("rhs_qq1 == %04X")(rhs_qq1);
	kmwritefln!("q0      == %04X")(q0);
	kmwritefln!("qq0     == %04X")(qq0);
	kmwritefln!("qq1     == %04X")(qq1);
	kmwritefln!("qq2     == %04X")(qq2);
	kmwritefln!("q2      == %04X")(q2);
	kmwriteln!("");

	// Note that `qq1` does not use all (n_bits) bits.
	// It uses, at most, ((n_bits/2)+1) bits, with the +1 only happening for carry.
	// This knowledge will help us avoid unnecessary operations later on
	// when we are accumulating the results.

	// Now we are far enough along to accumulate all of the components
	// into our resulting integers:
	//
	// result = q2*m^2 + q1*m + q0
	//
	// Now we need to repack {q0,q1,q2,...} into {result.lo,result.hi}:
	//
	//        q0 =             [bbbbbbaaaaaa]
	//       -q0 =       [ccccccbbbbbb]
	//       -q2 =       [ccccccbbbbbb]
	//       qq0 =                  [b]
	//       qq1 =             [ccbbb]
	//       qq2 =     [ddccccccbbbb]
	//        q2 = [ddddddcccccc]
	// result.lo =             [bbbbbbaaaaaa]
	// result.hi = [ddddddcccccc]
	//
	T q0_middle = q0;
	T q2_middle = q2;

	// First pass of accumulating digits into the high bits.
	q2 += qq2 >>> ((n_bits/2)-2);
	kmwriteln!("q2 += qq2 >>> ((n_bits/2)-2)");
	kmwritefln!("q2 == %04X")(q2);

	// q2 += qq1 >>> ((n_bits/2)-1); // <- unnecessary because of `qq1`'s narrow width*
	// q2 does not overlap with qq0
	q2 -= q2_middle >>> (n_bits/2);
	kmwriteln!("q2 -= q2_middle >>> (n_bits/2)");
	kmwritefln!("q2 == %04X")(q2);

	q2 -= q0_middle >>> (n_bits/2);
	kmwriteln!("q2 -= q0_middle >>> (n_bits/2)");
	kmwritefln!("q2 == %04X")(q2);


	// * The top couple bits of `qq1` DO need to make it into `q2`, but because
	//     `qq1` is only ((n_bits/2)+1) bits wide, it will fit entirely into
	//     the middle lane. We don't need to accumulate it into `q2` right away.
	//     So instead, we'll merge it into `mid` in a bit, and that will
	//     eventually merge its carry bits into `q2`, which will move the top
	//     bits of `qq1` into `q2` for free (by piggy-backing on other carry ops).

	// Accumulate half-width things in the "middle" lane.
	T mid;
	mid  = (qq2 & ((1 << ((n_bits/2)-2)) - 1)) << 2;
	kmwriteln!("mid = qq2 & ((1 << ((n_bits/2)-2)) - 1)) << 2");
	kmwritefln!("mid == %04X")(mid);

	//mid += (qq1 & ((1 << ((n_bits/2)+1)) - 1)) << 1;
	mid += qq1 << 1; // `qq1` only has ((n_bits/2)+1) bits, none of which overlap other sources, so we don't need to mask it.
	kmwriteln!("mid += qq1 << 1");
	kmwritefln!("mid == %04X")(mid);

	mid += qq0;
	kmwriteln!("mid += qq0");
	kmwritefln!("mid == %04X")(mid);

	mid += q0 >>> (n_bits/2);
	kmwriteln!("mid += q0 >>> (n_bits/2)");
	kmwritefln!("mid == %04X")(mid);

	// The top of `q0` just moved into `mid`.
	// We need to mask it out so that we can move summed data back into `q0` later.
	q0 &= lo_mask;
	kmwriteln!("q0 &= lo_mask");
	kmwritefln!("q0 == %04X")(q0);

	mid -= q0_middle & lo_mask;
	mid -= q2_middle & lo_mask;
	kmwriteln!("mid -= q0_middle & lo_mask;");
	kmwriteln!("mid -= q2_middle & lo_mask;");
	kmwritefln!("mid == %04X")(mid);

	// Do a _signed_ shift-right to calculate the carry-or-borrow that needs
	// to be added onto q2.
	// The signed shift will perform sign-extension, which is important if
	// `mid` ended up negative after all of its accumulation.
	// (Because the (q0_middle+q2_middle) that we just subtracted from `mid`
	// might have been greater than the other stuff that was added to `mid`.)
	// For instance, consider this scenario:
	// ```
	//     // q2 is 0x0BFF
	//     // q0_middle is 0x01FF
	//     // q2_middle is 0x01FF
	//     // mid is 0x00FD
	//     mid -= q0_middle & lo_mask; // mid is now (0x00FD-0x00FF) = 0xFFFE
	//     mid -= q2_middle & lo_mask; // mid is now (0xFFFE-0x00FF) = 0xFEFF
	//     ST carry_or_borrow = cast(ST)mid; // carry_or_borrow = 0xFEFF
	//     carry_or_borrow >>= (n_bits/2); // carry_or_borrow >>= 8; is now 0xFFFE == -2
	//     q2 += cast(T)carry_or_borrow; // q2 += 0xFFFE; -> q2 = 0x0BFF + 0xFFFE; -> q2 = 0x0BFF - 2; -> q2 = 0x0BFD
	//     // carry/borrow for mid-into-q2 is done.
	// ```
	import std.traits : Signed;
	alias ST = Signed!T;

	ST carry_or_borrow = cast(ST)mid;
	carry_or_borrow >>= (n_bits/2);
	kmwriteln!("ST carry_or_borrow = cast(ST)mid;");
	kmwriteln!("carry_or_borrow >>= (n_bits/2);");
	kmwritefln!("carry_or_borrow == %04X")(q2);

	// We cast back to an unsigned type before accumulating into `q2`, just
	// in case type-agreement matters. (Even if it doesn't here, it might help
	// someone write this in another language.)
	// Two's-complement addition will be the same operation regardless of the
	// signed-ness of either operand.
	q2 += cast(T)carry_or_borrow;
	kmwriteln!("q2 += cast(T)carry_or_borrow;");
	kmwritefln!("q2 == %04X")(q2);

	// The upper portions of q0_middle and q2_middle were already subtracted
	// from `q2` earlier. So we are done with `q0_middle` and `q2_middle`
	// at this point.

	// The bottom half of `mid` now represents the 2nd/4 quarter of our final answer.
	// The top half of `q0` was cleared early, so we are free to copy into it.
	q0 |= mid << (n_bits/2);
	kmwriteln!("q0 |= mid << (n_bits/2)");
	kmwritefln!("q0 == %04X")(q0);

	// At this point, everything has been accumulated into `q0` and `q2`,
	// so those variables hold our results.
	KaratsubaInteger!T  result;
	result.lo = q0;
	result.hi = q2;

	kmwritefln!("result.lo == %04X")(result.lo);
	kmwritefln!("result.hi == %04X")(result.hi);
	kmwritefln!("Finished `mult_karatsuba_full(lhs:%04X, rhs:%04X)`")(lhs, rhs);

	return result;
}




pure nothrow @nogc @safe
KaratsubaInteger!T  mult_karatsuba_full_neg(T)(T lhs, T rhs)
	if ( isIntegral!T && isUnsigned!T )
{
	// In the below implementation, you will see this pattern:
	//   q = (p + p_mask) ^ p_mask;
	// or
	//   q += p_mask;
	//   q ^= p_mask;
	//
	// This is a way to conditionally negate a twos-complement integer.
	// More specifically, it does the following operation:
	//
	//   if ( p < 0 )
	//       q = -p;
	//
	// Similarly, we can evaluate absolute values this way:
	//
	//   p = abs(p);
	//
	// ... is the same as:
	//
	//   p_mask = (cast(Signed!(typeof(p)))p) >> (n_bits-1);
	//   p = (p + p_mask) ^ p_mask;
	//
	// What these are doing is emulating twos-complement arithmatic:
	// To negate a twos-complement number, invert (flip) its bits, then add 1.
	// Alternatively: subtract 1, then invert its bits.
	//
	// We're using the alternative strategy because
	// the former version is patented.
	// Source and details: https://graphics.stanford.edu/~seander/bithacks.html#IntegerAbs
	// Also: https://stackoverflow.com/a/9962527/1261963  (This person probably knew about the bithacks sites)
	//
	// You might still notice that we are adding the mask, rather than subtracting 1.
	//
	// That's because it would take at least one extra instruction (per negation)
	// to compute the conditional `1` value. So, instead, we exploit this property:
	// (x - 1) == (x + -1) == (x + 0xFF)
	//
	// So we can always add or subtract 1 from a number by subtracting or adding
	// its (integer type's) mask value.
	//
	// And that is how the code below accomplishes branchless negation and absolute-ing.

	kmwritefln!("Debugging `mult_karatsuba_full(lhs:%04X, rhs:%04X)`")(lhs, rhs);

	import std.traits : Signed;
	alias ST = Signed!T;

	//enum T zero = cast(T)0;
	enum T one = cast(T)1;
	enum T n_bits = T.sizeof * 8;
	enum T lo_mask = (one << (n_bits/2)) - 1; // Ex: If (T==ushort) then (lo_mask=0x00FF);

	kmwriteln!("");
	kmwritefln!("typeof(T) == %s")(T.stringof);
	kmwritefln!("n_bits  == %d")  (n_bits);
	kmwritefln!("lo_mask == %04X")(lo_mask);

	T lhs_lo = cast(T)(lhs & lo_mask);
	T lhs_hi = cast(T)(lhs >>> (n_bits/2));
	T rhs_lo = cast(T)(rhs & lo_mask);
	T rhs_hi = cast(T)(rhs >>> (n_bits/2));

	ST lhs_sdiff = cast(ST)(lhs_lo - lhs_hi);
	ST rhs_sdiff = cast(ST)(rhs_hi - rhs_lo);
	T lhs_mask = cast(T)(lhs_sdiff >> (n_bits-1)); // extend sign bit to fill
	T rhs_mask = cast(T)(rhs_sdiff >> (n_bits-1)); // extend sign bit to fill
	T q1_mask = lhs_mask ^ rhs_mask; // output_sign = lhs_sign * rhs_sign;
	T lhs_diff = cast(T)((lhs_sdiff + lhs_mask) ^ lhs_mask); // = abs(lhs_sdiff);
	T rhs_diff = cast(T)((rhs_sdiff + rhs_mask) ^ rhs_mask); // = abs(rhs_sdiff);

	kmwriteln!("");
	kmwritefln!("lhs_lo  == %04X")(lhs_lo);
	kmwritefln!("lhs_hi  == %04X")(lhs_hi);
	kmwritefln!("rhs_lo  == %04X")(rhs_lo);
	kmwritefln!("rhs_hi  == %04X")(rhs_hi);
	kmwritefln!("lhs_sdf == %04X")(cast(T)lhs_sdiff);
	kmwritefln!("rhs_sdf == %04X")(cast(T)rhs_sdiff);
	kmwritefln!("lhs_msk == %04X")(lhs_mask);
	kmwritefln!("rhs_msk == %04X")(rhs_mask);
	kmwritefln!("lhs_dif == %04X")(lhs_diff);
	kmwritefln!("rhs_dif == %04X")(rhs_diff);
	kmwritefln!("q1_mask == %04X")(q1_mask);
	kmwriteln!("");

	T q0 = cast(T)(lhs_lo   * rhs_lo );
	T q1 = cast(T)(lhs_diff * rhs_diff);
	T q2 = cast(T)(lhs_hi   * rhs_hi );

	kmwritefln!("q0      == %04X")(q0);
	kmwritefln!("q1      == %04X")(q1);
	kmwritefln!("q2      == %04X")(q2);
	kmwriteln!("");

	// Here, we negate `q1`, but only if `lhs_sdiff * rhs_sdiff` would have
	// been negative.
	q1 += q1_mask;
	q1 ^= q1_mask;

	// The above isn't quite enough, because a negative `q1` would span "n_bits+1" bits.
	// So we have `q1_sign`, which is that extra bit.
	// `q1_sign` is that thing we must subtract from `q2` later, to emulate
	// the borrowing that would happen when a negative number is added to
	// its lower half.
	//
	// In most cases, we could compute it this way:
	// T q1_sign = (q1_mask & 1) << (n_bits/2);
	//
	// This usually works, because `q1_mask` has all bits set when the multiplication
	// goes negative, and all bits clear if it goes positive. Taking the lowest
	// bit of that will give us a 1 or 0 based on that condition.
	//
	// However, it doesn't work when q1==0. In that case, -0 == 0, and we shouldn't
	// subtract anything from `q2` later on, because there is no borrowing to
	// emulate when subtracting 0.
	//
	// To that end, we must AND `q1_mask` with a bit that will be 1 if `q1` is
	// nonzero, or 0 if `q1` is zero. And it has to be 1 or 0 specifically.
	// Any larger numbers may fail to include the lowest bit of `q1_mask`.
	// Because `q1` could be _anything_, we need to normalize it to 1 or 0.
	// We do that with the `!!q1` trick, which is equivalent to `0 < q1 ? 1 : 0`,
	// or to
	// ```
	// if ( 0 == q1 )
	//     q1_sign = 0;
	// else // 0 < q1
	//     q1_sign = q1_mask & 1;
	// ```
	//
	T q1_sign = q1_mask & !!q1;
	// Alternative version, if you're translating this code to some place
	// where `!!q1` isn't available, and you still need it to be branchless:
	//T q1_sign = q1_mask & ((q1 >>> (n_bits-1)) | (cast(T)(-q1) >>> (n_bits-1)));
	q1_sign <<= n_bits/2;
	kmwriteln!("q1 += q1_mask");
	kmwriteln!("q1 ^= q1_mask");
	kmwritefln!("q1      == %04X")(q1);
	kmwritefln!("q1_sign == %04X")(q1_sign);
	kmwriteln!("");

	// Now we are far enough along to accumulate all of the components
	// into our resulting integers:
	//
	// result = q2*m^2 + q1*m + q0
	//
	// Now we need to repack {q0,q1,q2,...} into {result.lo,result.hi}:
	//
	//        q0 =             [bbbbbbaaaaaa]
	// q0_middle =       [ccccccbbbbbb]
	//        q1 =       [ccccccbbbbbb]
	// q2_middle =       [ccccccbbbbbb]
	//  -q1_sign =      [d]
	//        q2 = [ddddddcccccc]
	// result.lo =             [bbbbbbaaaaaa]
	// result.hi = [ddddddcccccc]
	//
	T q0_middle = q0;
	alias q1_middle = q1;
	T q2_middle = q2;

	// First pass of accumulating digits into the high bits.

	q2 += q0_middle >>> (n_bits/2);
	kmwriteln!("q2 += q0_middle >>> (n_bits/2)");
	kmwritefln!("q2 == %04X")(q2);

	q2 += q1_middle >>> (n_bits/2);
	kmwriteln!("q2 += q1_middle >>> (n_bits/2)");
	kmwritefln!("q2 == %04X")(q2);

	q2 += q2_middle >>> (n_bits/2);
	kmwriteln!("q2 += q2_middle >>> (n_bits/2)");
	kmwritefln!("q2 == %04X")(q2);

	q2 -= q1_sign;
	kmwriteln!("q2 -= q1_sign");
	kmwritefln!("q2 == %04X")(q2);

	// Accumulate half-width things in the "middle" lane.
	q0_middle &= lo_mask;
	q1_middle &= lo_mask;
	q2_middle &= lo_mask;
	kmwriteln!("q0_middle &= lo_mask");
	kmwriteln!("q1_middle &= lo_mask");
	kmwriteln!("q2_middle &= lo_mask");

	q1_middle += q0_middle;
	q1_middle += q2_middle;
	q1_middle += q0 >>> (n_bits/2);
	kmwriteln!("q1_middle += q0_middle");
	kmwriteln!("q1_middle += q2_middle");
	kmwriteln!("q1_middle += q0 >>> (n_bits/2)");
	kmwritefln!("q1_middle == %04X")(q1_middle);

	// Update the top half of `q0`.
	// (We can mask it initially because the original contents have already
	// been accumulated into the bottom half of `q1_middle`. So this operation
	// won't lose any information.)
	q0 &= lo_mask;
	q0 |= q1_middle << (n_bits/2);
	kmwriteln!("q0 &= lo_mask");
	kmwriteln!("q0 |= q1_middle << (n_bits/2)");
	kmwritefln!("q0 == %04X")(q0);

	// Carry / overflow.
	q2 += q1_middle >>> (n_bits/2);
	kmwriteln!("q2 += q1_middle >>> (n_bits/2)");
	kmwritefln!("q2 == %04X")(q2);

	// At this point, everything has been accumulated into `q0` and `q2`,
	// so those variables hold our results.
	KaratsubaInteger!T  result;
	result.lo = q0;
	result.hi = q2;

	kmwritefln!("result.lo == %04X")(result.lo);
	kmwritefln!("result.hi == %04X")(result.hi);
	kmwritefln!("Finished `mult_karatsuba_full(lhs:%04X, rhs:%04X)`")(lhs, rhs);

	return result;
}

// As of this writing, it makes sense to either define this as
// `mult_karatsuba_full_neg` or `mult_karatsuba_full_pos`.
// They _should_ give the exact same results. The only difference is
// in the calculations used to reach those results.
// This alias allows us to easily switch between the implementations.
// Future directions: The unittests should probably test both
// at the same time, not just whichever is selected currently.
alias mult_karatsuba_full = mult_karatsuba_full_neg;

ulong mult_karatsuba(uint lhs, uint rhs)
{
	auto result = mult_karatsuba_full(lhs,rhs);
	ulong result_u64 = 0;
	result_u64 |= result.hi;
	result_u64 <<= 32;
	result_u64 |= result.lo;
	return result_u64;
}

uint mult_karatsuba(ushort lhs, ushort rhs)
{
	auto result = mult_karatsuba_full(lhs,rhs);
	uint result_u32 = 0;
	result_u32 |= result.hi;
	result_u32 <<= 16;
	result_u32 |= result.lo;
	return result_u32;
}

ushort mult_karatsuba(ubyte lhs, ubyte rhs)
{
	auto result = mult_karatsuba_full(lhs,rhs);
	ushort result_u16 = 0;
	result_u16 |= result.hi;
	result_u16 <<= 8;
	result_u16 |= result.lo;
	return result_u16;
}

unittest
{
	import std.format;
	import std.stdio;

	writeln("unittest mult_karatsuba");

	ubyte _00 = 0x00;
	ubyte _01 = 0x01;
	ubyte _0F = 0x0F;
	ubyte _10 = 0x10;
	ubyte _7F = 0x7F;
	ubyte _80 = 0x80;
	ubyte _FE = 0xFE;
	ubyte _FF = 0xFF;

	assert(0x0000 == mult_karatsuba(_00,_00));
	assert(0x0000 == mult_karatsuba(_00,_01));
	assert(0x0000 == mult_karatsuba(_01,_00));
	assert(0x0000 == mult_karatsuba(_00,_FF));
	assert(0x0000 == mult_karatsuba(_FF,_00));
	assert(0x0001 == mult_karatsuba(_01,_01));
	assert(0x000F == mult_karatsuba(_01,_0F));
	assert(0x000F == mult_karatsuba(_0F,_01));
	assert(0x00E1 == mult_karatsuba(_0F,_0F));
	assert(0x0010 == mult_karatsuba(_01,_10));
	assert(0x0010 == mult_karatsuba(_10,_01));
	assert(0x0100 == mult_karatsuba(_10,_10));
	assert(0x4000 == mult_karatsuba(_80,_80));
	assert(0x3F01 == mult_karatsuba(_7F,_7F));
	assert(0xFC04 == mult_karatsuba(_FE,_FE));
	assert(0xFD02 == mult_karatsuba(_FE,_FF));
	assert(0xFD02 == mult_karatsuba(_FF,_FE));
	assert(0xFE01 == mult_karatsuba(_FF,_FF));
	assert(0x7E81 == mult_karatsuba(_7F,_FF));
	assert(0x7F80 == mult_karatsuba(_80,_FF));
	assert(0x3F80 == mult_karatsuba(_80,_7F));

	for ( ushort i = 0; i < 256; i++ )
	{
		for ( ushort j = 0; j < 256; j++ )
		{
			ushort expected = cast(ushort)(i*j);
			ushort got = mult_karatsuba(cast(ubyte)i, cast(ubyte)j);
			if ( expected != got ) {
				debug_printing = true;
				got = mult_karatsuba(cast(ubyte)i, cast(ubyte)j);
			}
			assert(expected == got, format("Operands: i=%02x; j=%02x; Expected: %04x; Got: %04X", i, j, expected, got));
		}
	}

	ushort _0000 = 0x0000;
	ushort _0001 = 0x0001;
	ushort _FFFF = 0xFFFF;

	assert(0x0000_0000 == mult_karatsuba(_0000,_0000));
	assert(0x0000_0000 == mult_karatsuba(_0000,_0001));
	assert(0x0000_0000 == mult_karatsuba(_0001,_0000));
	assert(0x0000_0000 == mult_karatsuba(_0000,_FFFF));
	assert(0x0000_0000 == mult_karatsuba(_FFFF,_0000));
	assert(0x0000_0001 == mult_karatsuba(_0001,_0001));
	assert(0x0000_FFFF == mult_karatsuba(_0001,_FFFF));
	assert(0x0000_FFFF == mult_karatsuba(_FFFF,_0001));
	assert(0xFFFE_0001 == mult_karatsuba(_FFFF,_FFFF));

	uint _0000_0000 = 0x0000_0000;
	uint _0000_0001 = 0x0000_0001;
	uint _FFFF_FFFF = 0xFFFF_FFFF;

	assert(0x0000_0000_0000_0000_UL == mult_karatsuba(_0000_0000,_0000_0000));
	assert(0x0000_0000_0000_0000_UL == mult_karatsuba(_0000_0000,_0000_0001));
	assert(0x0000_0000_0000_0000_UL == mult_karatsuba(_0000_0001,_0000_0000));
	assert(0x0000_0000_0000_0000_UL == mult_karatsuba(_0000_0000,_FFFF_FFFF));
	assert(0x0000_0000_0000_0000_UL == mult_karatsuba(_FFFF_FFFF,_0000_0000));
	assert(0x0000_0000_0000_0001_UL == mult_karatsuba(_0000_0001,_0000_0001));
	assert(0x0000_0000_FFFF_FFFF_UL == mult_karatsuba(_0000_0001,_FFFF_FFFF));
	assert(0x0000_0000_FFFF_FFFF_UL == mult_karatsuba(_FFFF_FFFF,_0000_0001));
	assert(0xFFFF_FFFE_0000_0001_UL == mult_karatsuba(_FFFF_FFFF,_FFFF_FFFF));

	// Explicit test of struct-returning version, and of 64-bit inputs.
	ulong  a64 = 0xAceBe11e_CafeBabe_UL;
	ulong  b64 = 0xF100fCa7_F1edFa57_UL;
	KaratsubaInteger!ulong  r128 = mult_karatsuba_full(a64,b64);
	assert(0x8E9C_2945_7ED5_0292 == r128.lo);
	assert(0xA2CA_B997_9FFE_C71C == r128.hi);

	// Guarantee functioning at compile-time.
	enum ushort a16 = 0xF00F;
	enum ushort b16 = 0xB00F;
	enum uint r32 = mult_karatsuba(a16,b16);
	static assert(0XA51860E1 == r32);

	writeln("unittest mult_karatsuba: done");
}
