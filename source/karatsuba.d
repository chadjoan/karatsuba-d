module karatsuba_d;

struct KaratsubMultiplyResult(T)
{
	T  lo;
	T  hi;
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
			if ( debug_printing )
				writeln(ln);
		}
	}

	void kmwritefln(string fmtstr, A...)(A args)
	{
		debug {
			if ( debug_printing )
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

import std.traits;

pure nothrow @nogc @safe
KaratsubMultiplyResult!T  mult_karatsuba_full(T)(T lhs, T rhs)
	if ( isIntegral!T && isUnsigned!T )
{
	kmwritefln!("Debugging `mult_karatsuba_full(lhs:%04X, rhs:%04X)`")(lhs, rhs);

	enum n_bits = T.sizeof * 8;
	enum lo_mask = (1 << (n_bits/2)) - 1; // Ex: If (T==ushort) then (lo_mask=0x00FF);

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
/+
	T oflow;
	oflow  = lhs_sum >>> (n_bits/2);
	oflow &= rhs_sum >>> (n_bits/2);
	kmwriteln!("");
	kmwritefln!("oflow   == %04X")(oflow);
+/
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

	/+
	lhs_sum &= lo_mask;
	rhs_sum &= lo_mask;
	+/

/+
	// (0xFF+0xFF)*(0xFF+0xFF) = 0x3F804 // 4/4 high bits set
	// (0xFF+0xFF)*(0xFF+0x7F) = 0x2F904 // 3/4 high bits set
	// (0xFF+0x7F)*(0xFF+0x7F) = 0x23A04 // 2/4 high bits set (in different factors)
	// (0xFF+0xFF)*(0x7F+0x7F) = 0x1FA04 // 2/4 high bits set (in same factor)
	// (0xFF+0x7F)*(0x7F+0x7F) = 0x17B04 // 1/4 high bits set
	// (0x7F+0x7F)*(0x7F+0x7F) = 0x0FC04 // 0/4 high bits set

	// (0xFF-0xFF)*(0xFF-0xFF) = 0x00000 // 4/4 high bits set
	// (0xFF-0xFF)*(0xFF-0x7F) = 0x00000 // 3/4 high bits set
	// (0xFF-0xFF)*(0x7F-0xFF) = 0x00000 // 3/4 high bits set
	// (0xFF-0x7F)*(0xFF-0x7F) = 0x23A04 // 2/4 high bits set (in different factors)
	// (0x7F-0xFF)*(0x7F-0xFF) = 0x23A04 // 2/4 high bits set (in different factors)
	// (0xFF-0x7F)*(0x7F-0xFF) = 0x23A04 // 2/4 high bits set (in different factors)
	// (0x7F-0xFF)*(0xFF-0x7F) = 0x23A04 // 2/4 high bits set (in different factors)
	// (0xFF-0xFF)*(0x7F-0x7F) = 0x00000 // 2/4 high bits set (in same factor)
	// (0xFF-0x7F)*(0x7F-0x7F) = 0x00000 // 1/4 high bits set
	// (0x7F-0xFF)*(0x7F-0x7F) = 0x00000 // 1/4 high bits set
	// (0x7F-0x7F)*(0x7F-0x7F) = 0x00000 // 0/4 high bits set
	question:
	x = (a + b) | (c + d)
	y = (a | b) + (c | d)
	z = (a + b) + (c + d)
	w = (a + b) & (c + d)
	u = (a & b) + (c & d)
	v = (a & b & c & d)
	q = ((a + b) | (c + d)) + ((a + b) & (c + d)) = y+w
	r = ((a | b) + (c | d)) | (a & b & c & d) = y+v = works!
	s = ((a | b) + (a & b)) + ((c | d) + (c & d)) = nope
	p = (a | b | c | d) + (a & b) + (c & d) = almost but no
	k = (a | b | c | d) + (a & c) + (b & d) = works!
	n = ((a + b) | a | b) | ((c + d) | c | d)
	abc



	a,b
	a,c
	a,d
	b,c
	b,d
	c,d

	t = (a | c) + (b | d)
	x ?= y
| a : b : c : d : tg :a+b :c+d :a+c :b+d :a+d :b+c |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 01 : 00 : 01 : 01 : 00 |
| 0 : 0 : 1 : 1 : 01 : 00 : 10 : 01 : 01 : 01 : 01 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 01 : 10 : 01 : 01 |
| 0 : 1 : 1 : 1 : 10 : 01 : 10 : 10 : 10 : 01 : 10 |
| 1 : 1 : 1 : 1 : 11 : 10 : 10 : 10 : 10 : 10 : 10 |

| a : b : c : d : tg :a&b :c&d :a&c :b&d :a&d :b&c |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 1 : 1 : 01 : 00 : 01 : 00 : 00 : 00 : 00 |
| 0 : 1 : 0 : 1 : 10 : 00 : 00 : 00 : 01 : 00 : 00 |
| 0 : 1 : 1 : 1 : 10 : 00 : 01 : 00 : 01 : 00 : 01 |
| 1 : 1 : 1 : 1 : 11 : 01 : 01 : 01 : 01 : 01 : 01 |

| a : b : c : d : tg :a|b :c|d :a|c :b|d :a|d :b|c |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 01 : 00 : 01 : 01 : 00 |
| 0 : 0 : 1 : 1 : 01 : 00 : 01 : 01 : 01 : 01 : 01 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 00 : 01 : 01 : 01 |
| 0 : 1 : 1 : 1 : 10 : 01 : 01 : 01 : 01 : 01 : 01 |
| 1 : 1 : 1 : 1 : 11 : 01 : 01 : 01 : 01 : 01 : 01 |

| a : b : c : d : tg :a^b :c^d :a^c :b^d :a^d :b^c |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 01 : 00 : 01 : 01 : 00 |
| 0 : 0 : 1 : 1 : 01 : 00 : 00 : 01 : 01 : 01 : 01 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 00 : 00 : 01 : 01 |
| 0 : 1 : 1 : 1 : 10 : 01 : 00 : 01 : 00 : 01 : 00 |
| 1 : 1 : 1 : 1 : 11 : 00 : 00 : 00 : 00 : 00 : 00 |

AB + AC(A+B)
NAND
| a : b : c : d : tg : ab : cd : ac : bd : ad : bc |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 01 : 01 : 01 : 01 : 01 : 01 |
| 0 : 0 : 0 : 1 : 01 : 01 : 00 : 01 : 00 : 00 : 01 |
| 0 : 0 : 1 : 1 : 01 : 01 : 00 : 00 : 00 : 00 : 00 |
| 0 : 1 : 0 : 1 : 10 : 00 : 00 : 01 : 00 : 00 : 00 |
| 0 : 1 : 1 : 1 : 10 : 00 : 00 : 00 : 00 : 00 : 00 |
| 1 : 1 : 1 : 1 : 11 : 00 : 00 : 00 : 00 : 00 : 00 |

PLUS? Actually not as free as I thought.
| a : b : c : d : tg : ab : cd |
+---+---+---+---+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 01 |
| 0 : 0 : 1 : 1 : 01 : 00 : 00 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 |
| 0 : 1 : 1 : 1 : 10 : 01 : 00 |
| 1 : 1 : 1 : 1 : 11 : 00 : 00 |

(a+c-b+d)
| a : b : c : d : tg : ac : xx |
+---+---+---+---+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 01 |
| 0 : 0 : 1 : 1 : 01 : 01 : 10 |
| 0 : 1 : 0 : 1 : 10 : 00 : 11 |
| 0 : 1 : 1 : 1 : 10 : 01 : 01 |
| 1 : 1 : 1 : 1 : 11 : 10 : 10 |

+1+
| a : b : c : d : tg : ab : cd : xx |
+---+---+---+---+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 01 : 01 : 00 |
| 0 : 0 : 0 : 1 : 01 : 01 : 10 : 11 |
| 0 : 0 : 1 : 1 : 01 : 01 : 11 : 10 |
| 0 : 1 : 0 : 1 : 10 : 10 : 10 : 00 |
| 0 : 1 : 1 : 1 : 10 : 10 : 11 : 01 |
| 1 : 1 : 1 : 1 : 11 : 11 : 11 : 00 |

AND+1
| a : b : c : d : tg : ab : cd : ac : bd : xx |
+---+---+---+---+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 01 : 01 : 01 : 01 : 00 |
| 0 : 0 : 0 : 1 : 01 : 01 : 01 : 01 : 01 : 00 |
| 0 : 0 : 1 : 1 : 01 : 01 : 10 : 01 : 01 : 00 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 01 : 10 : 11 |
| 0 : 1 : 1 : 1 : 10 : 01 : 10 : 01 : 10 : 11 |
| 1 : 1 : 1 : 1 : 11 : 10 : 10 : 10 : 10 : 00 |

g = (((a | b) + (c | d)) | a | b | c | d) = y | a | b | c | d
h = (a ^ b ^ c ^ d)
i = (((a ^ b) + (c ^ d)) | (a ^ b ^ c ^ d))

| a : b : c : d : tg :  y :  x :  w :  u :  v :  q :  r :  z :  g :  h :  h |
+---+---+---+---+----+----+----+----+----+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 01 : 01 : 00 : 00 : 00 : 01 : 01 : 01 : 01 : 01 : 01 |
| 0 : 0 : 1 : 1 : 01 : 01 : 10 : 00 : 01 : 00 : 10 : 01 : 10 : 01 : 00 : 00 |
| 0 : 1 : 0 : 1 : 10 : 10 : 01 : 01 : 00 : 00 : 11 : 10 : 10 : 11 : 00 : 10 |
| 0 : 1 : 1 : 1 : 10 : 10 : 11 : 00 : 01 : 00 : 10 : 10 : 11 : 11 : 01 : 01 |
| 1 : 1 : 1 : 1 : 11 : 10 : 10 : 11 : 10 : 01 :110 : 11 :100 : 11 : 00 : 00 |

z-u should work...
z = (a + b) + (c + d)
u = (a & b) + (c & d)

z-u = (a + b + c + d) - ((a & b) + (c & d))
z-u = (a + b + c + d) - (a & b) - (c & d)
z-u = (a - (a & b) + b) + (c - (c & d) + d)

| a : b : ab | ex |
+---+---+----+----+
| 0 : 0 : 00 : 00 |
| 0 : 1 : 00 : 01 |
| 1 : 0 : 00 : 01 |
| 1 : 1 : 01 : 01 |
... no commutative property :/
Also incorrect, because 4-2=2, not 3.


	ac = (a + c) 
	bd = (b + d)
	ac'= (a & c)
	bd'= (b & d)
	acr= (a | c)
	bdr= (b | d)
	acx= (a ^ c)
	bdx= (b ^ d)
	
a = (a + b) ^ b

| a : b : ab | ex |
+---+---+----+----+
| 0 : 0 : 00 : 00 |
| 0 : 1 : 01 : 00 |
| 1 : 0 : 01 : 01 |
| 1 : 1 : 10 : 11 |

l = (((a + b) ^ b) + c) ^ c) + d) ^ d)


| a : b : c : d : tg : a1 : x1 : a2': x2': a3 : x3 |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 00 : 00 : 00 : 01 : 00 |
| 0 : 0 : 1 : 1 : 01 : 00 : 00 : 01 : 00 : 01 : 00 |
| 0 : 1 : 0 : 1 : 10 : 01 : 00 : 00 : 00 : 01 : 00 |
| 0 : 1 : 1 : 1 : 10 : 01 : 00 : 01 : 00 : 01 : 00 |
| 1 : 1 : 1 : 1 : 11 : 10 : 11 : 10 : 11 : 10 : 00 |

l = (((a + b) | a) + c) | b) + d) | c)

| a : b : c : d : tg : a1 : r1 : a2': r2': a3 : r3 |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 00 : 00 : 00 : 01 : 01 |
| 0 : 0 : 1 : 1 : 01 : 00 : 00 : 01 : 01 : 10 : 11 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 00 : 01 : 10 : 10 |
| 0 : 1 : 1 : 1 : 10 : 01 : 01 : 10 : 11 :100 :101 |
| 1 : 1 : 1 : 1 : 11 : 01 : 01 : 10 : 11 :100 :101 |

l = (((a + c) | a) + b) & c) + d) | b)

| a : b : c : d : tg : a1 : r1 : a2': r2': a3 : r3 |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 00 : 00 : 00 : 01 : 01 |
| 0 : 0 : 1 : 1 : 01 : 01 : 01 : 01 : 01 : 10 : 10 | //stopped
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 00 : 01 : 10 : 10 |
| 0 : 1 : 1 : 1 : 10 : 01 : 01 : 10 : 11 :100 :101 |
| 1 : 1 : 1 : 1 : 11 : 01 : 01 : 10 : 11 :100 :101 |

r0 = 0
r0 = a & c
r0 <<= 1
r1 = 0
r1 = b & d
r1 <<= 1


| a : b : c : d : tg : ac : bd : ac': bd': acr: bdr: acx: bdx:  t :  s :  p :  k :  n |
+---+---+---+---+----+----+----+----+----+----+----+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 00 : 01 : 00 : 00 : 00 : 01 : 00 : 01 : 01 : 01 : 01 : 01 : 01 |
| 0 : 0 : 1 : 1 : 01 : 01 : 01 : 00 : 00 : 01 : 01 : 01 : 01 : 10 : 10 : 10 : 01 : 11 |
| 0 : 1 : 0 : 1 : 10 : 00 : 10 : 00 : 01 : 00 : 01 : 00 : 00 : 10 : 10 : 01 : 10 : 01 |
| 0 : 1 : 1 : 1 : 10 : 01 : 10 : 01 : 00 : 01 : 01 : 01 : 00 : 10 : 11 : 10 : 10 :100 |
| 1 : 1 : 1 : 1 : 11 : 10 : 10 : 01 : 01 : 01 : 01 : 00 : 00 : 10 :100 : 11 : 11 :110 |

| a : b : c : d : tg :  x :  w :  w :  q :  y :  z |
+---+---+---+---+----+----+----+----+----+----+----+
| 0 : 0 : 0 : 0 : 00 : 00 : 00 : 00 : 00 : 00 : 00 |
| 0 : 0 : 0 : 1 : 01 : 01 : 00 : 00 : 01 : 01 : 01 |
| 0 : 0 : 1 : 0 : 01 : 01 : 00 : 00 : 01 : 01 : 01 |
| 0 : 0 : 1 : 1 : 01 : 10 : 00 : 00 : 10 : 01 : 10 |
| 0 : 1 : 0 : 0 : 01 : 01 : 00 : 00 : 01 : XX : 01 |
| 0 : 1 : 0 : 1 : 10 : 01 : 01 : 01 : 10 : XX : 10 |
| 0 : 1 : 1 : 0 : 10 : 01 : 01 : 01 : 10 : XX : 10 |
| 0 : 1 : 1 : 1 : 10 : 11 : 00 : 00 : 11 : XX : 11 |
| 1 : 0 : 0 : 0 : 01 : 01 : 00 : 00 : 01 : XX : 01 |
| 1 : 0 : 0 : 1 : 10 : 01 : 01 : 01 : 10 : XX : 10 |
| 1 : 0 : 1 : 0 : 10 : 01 : 01 : 01 : 10 : XX : XX |
| 1 : 0 : 1 : 1 : 10 : 11 : 00 : 00 : 11 : XX : XX |
| 1 : 1 : 0 : 0 : 01 : 10 : 00 : 00 : 10 : XX : XX |
| 1 : 1 : 0 : 1 : 10 : 11 : 00 : 00 : 11 : XX : XX |
| 1 : 1 : 1 : 0 : 10 : 11 : 00 : 00 : 11 : XX : XX |
| 1 : 1 : 1 : 1 : 11 : 10 : 11 : 11 :101 : XX : XX |

	T carry = 0;
	carry += lhs_lo >>> (n_bits-1);
	carry += lhs_hi >>> (n_bits-1);
+/

	kmwriteln!("");
	kmwritefln!("lhs_lo  == %04X")(lhs_lo);
	kmwritefln!("lhs_hi  == %04X")(lhs_hi);
	kmwritefln!("rhs_lo  == %04X")(rhs_lo);
	kmwritefln!("rhs_hi  == %04X")(rhs_hi);
	kmwriteln!("");
	kmwritefln!("lhs_sum == %04X")(lhs_sum);
	kmwritefln!("rhs_sum == %04X")(rhs_sum);
	kmwriteln!("");

	// This multiply can put q1 out of range, but we handle this later
	// on by OR-ing the high bits of the operands together and adding
	// it to the q1 overflow.
	T q0  = cast(T)(lhs_lo  * rhs_lo );
	T qq2 = cast(T)(lhs_sum * rhs_sum);
	T q2  = cast(T)(lhs_hi  * rhs_hi );

	kmwritefln!("q0.0    == %04X")(q0);
	//kmwritefln!("qq0     == %04X")(qq0);
	//kmwritefln!("qq1     == %04X", qq1);
	kmwritefln!("qq2     == %04X")(qq2);
	//kmwritefln!("q1.0    == %04X")(q1);
	kmwritefln!("q2.0    == %04X")(q2);
	kmwriteln!("");
/+
/+
	// Borrowing logic:
	// if ( 0 < oflow && q2+q0 > q1 )
	//     oflow = 0;
	//
	// Branchless borrowing logic, setup:
	T msb_before;
	T msb_after;
	T msb_borrow_mask = (cast(T)(1)) << (n_bits-1);

	msb_before = q1;
+/
	q1 -= q0;
	kmwriteln!("q1 -= q0;");
	kmwritefln!("q1.1    == %04X")(q1);
/+
	msb_after = q1;
	msb_borrow_mask &= msb_before | ~msb_after;
	kmwritefln!("msb_b4  == %04X")(msb_before >>> (n_bits-1));
	kmwritefln!("msb_aft == %04X")(msb_after >>> (n_bits-1));
	kmwritefln!("msb_msk == %04X")(msb_borrow_mask >>> (n_bits-1));
	msb_before = q1;
+/
	q1 -= q2;
	kmwriteln!("q1 -= q2;");
	kmwritefln!("q1.2    == %04X")(q1);
	kmwriteln!("");
/+
	// Branchless borrowing, continued:
	msb_after = q1;
	msb_borrow_mask &= msb_before | ~msb_after;
	kmwritefln!("msb_b4  == %04X")(msb_before >>> (n_bits-1));
	kmwritefln!("msb_aft == %04X")(msb_after >>> (n_bits-1));
	kmwritefln!("msb_msk == %04X")(msb_borrow_mask >>> (n_bits-1));

	msb_borrow_mask >>>= (n_bits-1);
	kmwritefln!("msb_msk == %04X")(msb_borrow_mask);
	oflow &= msb_borrow_mask;
	kmwritefln!("oflow   == %04X")(oflow);
	kmwriteln!("");
+/
	// The above branchless logic works by... (TODO explain) (DONE: it didn't work, alt route used.)
	kmwritefln!("q0.0    == %04X")(q0);
	kmwritefln!("q1.3    == %04X")(q1);
	kmwritefln!("q2.0    == %04X")(q2);
	kmwriteln!("");
+/
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
	enum T firestop_bit = (1 << (n_bits/2)); // Stop carry propagation just past the first mask bit.
	enum T _ffffffff = cast(T)(-(cast(T)1));
	enum T premask = _ffffffff ^ firestop_bit;

	kmwritefln!("firestp == %04X")(firestop_bit);
	kmwritefln!("fffffff == %04X")(_ffffffff);
	kmwritefln!("premask == %04X")(premask);

	T lhs_mask = cast(T) ~(premask + rhs_lsb);
	T rhs_mask = cast(T) ~(premask + lhs_lsb);

	// If we wanted perfect masks, we would need to mask out the firestop bit
	// in ONLY the (lsb==0) case, because the mask will look something like
	// 0x0200 for n_bits==16.
	// But because the largest value from either sum is ((n_bits/2)+1), we can
	// safely ignore the extraneous mask bit. It won't do anything.

	//T lhs_mask = cast(T)((rhs_lsb << ((n_bits/2)+1)) - 1);
	//T rhs_mask = cast(T)((lhs_lsb << ((n_bits/2)+1)) - 1);

	T lhs_qq1 = lhs_sum & lhs_mask;
	T rhs_qq1 = rhs_sum & rhs_mask;

	T qq1 = cast(T)(lhs_qq1 + rhs_qq1);

	kmwritefln!("lhs_lsb == %04X")(lhs_lsb);
	kmwritefln!("rhs_lsb == %04X")(rhs_lsb);
	kmwritefln!("lhsmask == %04X")(lhs_mask);
	kmwritefln!("rhsmask == %04X")(rhs_mask);
	kmwritefln!("lhs_qq1 == %04X")(lhs_qq1);
	kmwritefln!("rhs_qq1 == %04X")(rhs_qq1);
	kmwritefln!("qq0     == %04X")(qq0);
	kmwritefln!("qq1     == %04X")(qq1);
	kmwritefln!("qq2     == %04X")(qq2);
	kmwriteln!("");

	// Note that `qq1` does not use all (n_bits) bits.
	// It uses, at most, ((n_bits/2)+1) bits, with the +1 only happening for carry.
	// This knowledge will help us avoid unnecessary operations later on
	// when we are accumulating the results.

/+ // Obsolete comments.
	// We don't need to do any 
	// qq2 === q1

	// TODO: need to subtract q0 and q2 from q1 AFTER the wide inner-product `q1` is computed.
/+
| b4 : aft : tg : x : y : a : b|~a |
+----+-----+----+---+---+---+------+
|  0 :  0  :  0 : 0 : 0 : 0 :   1  |
|  0 :  1  :  1 : 1 : 1 : 1 :   0  |
|  1 :  0  :  0 : 1 : 0 : 0 :   1  |
|  1 :  1  :  0 : 0 : 1 : 0 :   1  |
+/	
+/
/+
	// TODO: Optimization:
	// My first version was "OOPS ALL SHIFTS"
	// But that can be suboptimal, because then the shifters end up congested
	// while all of the other ALU circuits sit idle.
	// Ideally, we give the processor an opportunity to process one instruction
	// in the shifter while simultaneously processing another in the ANDer.
	// (Instruction Level Parallelism)
	// The below might still be suboptimal, because it does some shifting
	// right after some other shifting. Maybe it would be better to go
	// shift->and->shift. So we would start by shifting the MSB to the
	// desired position, then AND with masks that select the shifted MSB,
	// then finally do our table shifting (and masking).
	// Perhaps not all processors would take advantage of that, but
	// the ones that don't will probably not be hurt by it.

	// These formulas were verified as correct, using truth tables:
	//   overflow = (a | b | c | d) + (a & c) + (b & d)
	//   overflow = (a & b & c & d) | ((a | b) + (c | d))
	//
	// The downside to those is that they require computing intermediate values.
	//
	// The code below will avoid intermediate values by emulating a table-lookup
	// using bitwise arithmatic.

	// Clear all bits except for each highest bit (the msb).
	// (The msb is the one that is responsible for overflow.)
	enum T msb_mask = (1 << (n_bits-1)); // msb = most-significant-bit
	lhs_lo &= msb_mask;
	lhs_hi &= msb_mask;
	rhs_lo &= msb_mask;
	rhs_hi &= msb_mask;

	// Shift the msb down to a position where it can be used as a shift index.
	// Ex:
	// lhs_lo = 0b?0000000 -> 0b00000010 =  2
	// lhs_hi = 0b?0000000 -> 0b00000100 =  4
	// rhs_lo = 0b?0000000 -> 0b00001000 =  8
	// rhs_hi = 0b?0000000 -> 0b00010000 = 16
	lhs_lo >>>= (n_bits - 2); // *  2
	lhs_hi >>>= (n_bits - 3); // *  4
	rhs_lo >>>= (n_bits - 4); // *  8
	rhs_hi >>>= (n_bits - 5); // * 16

	enum uint oflow_table = 0b11_10_10_01__10_10_10_01__10_10_10_01__01_01_01_00;
	uint oflow = oflow_table;
	writefln("oflow   == %04X", oflow);
	oflow >>>= lhs_lo;
	writefln("oflow   == %04X", oflow);
	oflow >>>= lhs_hi;
	writefln("oflow   == %04X", oflow);
	oflow >>>= rhs_lo;
	writefln("oflow   == %04X", oflow);
	oflow >>>= rhs_hi;
	writefln("oflow   == %04X", oflow);
	oflow &= 3;
	writefln("oflow   == %04X", oflow);
	writeln("");

	// The above `table` variable encodes this table:
	//
	// | a : b : c : d : tg |
	// +---+---+---+---+----+
	// | 0 : 0 : 0 : 0 : 00 |
	// | 0 : 0 : 0 : 1 : 01 |
	// | 0 : 0 : 1 : 0 : 01 |
	// | 0 : 0 : 1 : 1 : 01 |
	// | 0 : 1 : 0 : 0 : 01 |
	// | 0 : 1 : 0 : 1 : 10 |
	// | 0 : 1 : 1 : 0 : 10 |
	// | 0 : 1 : 1 : 1 : 10 |
	// | 1 : 0 : 0 : 0 : 01 |
	// | 1 : 0 : 0 : 1 : 10 |
	// | 1 : 0 : 1 : 0 : 10 |
	// | 1 : 0 : 1 : 1 : 10 |
	// | 1 : 1 : 0 : 0 : 01 |
	// | 1 : 1 : 0 : 1 : 10 |
	// | 1 : 1 : 1 : 0 : 10 |
	// | 1 : 1 : 1 : 1 : 11 |

	// TODO: Where to stick it?
+/
	// TODO: Should probably do it the opposite of the below.
	// So, rather than adding the least significant things together first,
	// we should add the most significant things first. This frees up
	// space in the lower variables, which allows overflow to propagate
	// into them. After overflow propagation, we can move things back
	// to where they belong (as necessary).
	
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
	// Old:
	//     oflow =             [a]
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
/+
	// Move-and-add any carry bits from the top-half of `mid` into `q2` (high lane).
	// This is important because we'll need those bits in `mid` to be clear
	// so that its borrow logic can work without destroying our carry results.
	q2 += mid >>> (n_bits/2);
	mid &= lo_mask;
	kmwriteln!("q2 += mid >>> (n_bits/2)");
	kmwriteln!("mid &= lo_mask");
	kmwritefln!("q2 == %04X")(q2);
	kmwritefln!("mid == %04X")(mid);

	// But what if we need to borrow?
	// Subtracting q0 and q2 becomes tricky, because if the above adds didn't
	// contribute much, and q0 and q2's lower halves end up being big, then
	// subtracting them from `mid` will cause it to wrap around. That's fine,
	// but when the wrap happens, it should "borrow" a bit from the number
	// above it (q2).
	//
	
	
	// We rely on twos-complement math to ensure that adding any negative
	// overflow (wrap around) from `mid` into `q2` will be equivalent to
	// subtracting a borrow bit.
	//
	// Ex:
	// Suppose `mid == 0x01`, `q0_middle == 0xFF`, `q2_middle == 0xFF`,
	// `q2 == 0x10` and `n_bits == 8`.
	// 
/+
	import std.traits : Signed;
	alias ST = Signed!T;

	mid -= q0_middle;
	mid -= q2_middle;

	ST shifter = cast(ST)mid;
	shifter >>= (n_bits/2);

	T tmp = cast(T)shifter;
	q2 += tmp;
	// TODO: The twos-complement doesn't work!
	// 0x01-0xFF = 0x02; which overflows, but won't subtract shit when added to something else!
+/
	// To do the subtractions to the "middle" lane (`mid`), we will need to
	// implement some "borrow" logic to decrement the upper lane when appropriate.
	// TODO: Does this still work if `mid` has upper-half contents?
	// I think it will fail. We probably need to make this disable itself somehow
	// whenever the upper-half has bits, becuase the subtraction will just
	// borrow from those instead!
	// 
	// On systems that support branchless comparison, just do this:
	// T borrow = !!(mid < q0_middle);
	// mid -= q0_middle;
	// borrow += !!(mid < q2_middle);
	// mid -= q2_middle;
	//
	T borrow;
	borrow  = (((mid ^ q0_middle) & q0_middle) >>> ((n_bits/2)-1)) & 1;
	mid -= q0_middle;
	kmwriteln!("borrow  = ((mid ^ q0_middle) & q0_middle) >>> ((n_bits/2)-1)");
	kmwriteln!("mid -= q0_middle");
	kmwritefln!("borrow == %04X")(borrow);
	kmwritefln!("mid    == %04X")(mid);
	borrow += (((mid ^ q2_middle) & q2_middle) >>> ((n_bits/2)-1)) & 1;
	mid -= q2_middle;
	kmwriteln!("borrow += ((mid ^ q2_middle) & q2_middle) >>> ((n_bits/2)-1)");
	kmwriteln!("mid -= q2_middle");
	kmwritefln!("borrow == %04X")(borrow);
	kmwritefln!("mid    == %04X")(mid);
	q2 -= borrow;
	kmwriteln!("q2 -= borrow");
	kmwritefln!("q2 == %04X")(q2);

	// Table with examples of what the above logical operations are doing,
	// with `x === mid` and `y === qN_middle`.
	// The `b` column is 1 when borrowing happens, and 0 when it doesn't.
	// (We can't USE `b`, rather, we must _predict_ what it will be, using `x`, `y`, and `r`.)
	// The single-bit `x` and `y` columns represent the msb of `x` and `y`.
	// `r` is the msb of the result of the subtraction (msb of `res`).
	//
	// |            : res  :   :msb:msb:msb|
	// |  x  -  y   :  = r : b : x : y : r |
	// +------------+------+---+---+---+---+
	// | 0x01-0x01  : 0x00 : 0 : 0 : 0 : 0 |
	// | 0x7F-0x7F  : 0x00 : 0 : 0 : 0 : 0 |
	// | Impossible :  N/A : 0 : 0 : 0 : 1 |
	// | Impossible :  N/A : 0 : 0 : 1 : 0 |
	// | Impossible :  N/A : 0 : 0 : 1 : 1 |
	// | 0x80-0x7F  : 0x01 : 0 : 1 : 0 : 0 |
	// | 0xFF-0x01  : 0xFE : 0 : 1 : 0 : 1 |
	// | 0x80-0x80  : 0x00 : 0 : 1 : 1 : 0 |
	// | 0xFF-0x80  : 0x7F : 0 : 1 : 1 : 0 |
	// | 0xFF-0xFF  : 0x00 : 0 : 1 : 1 : 0 |
	// | Impossible :  N/A : 0 : 1 : 1 : 1 |
	// | Impossible :  N/A : 1 : 0 : 0 : 0 |
	// | 0x00-0x7F  : 0x81 : 1 : 0 : 0 : 1 |
	// | 0x00-0x01  : 0xFF : 1 : 0 : 0 : 1 |
	// | 0x01-0xFF  : 0x02 : 1 : 0 : 1 : 0 |
	// | 0x7E-0xFF  : 0x7F : 1 : 0 : 1 : 0 |
	// | 0x00-0x80  : 0x80 : 1 : 0 : 1 : 1 |
	// | 0x7F-0x80  : 0xFF : 1 : 0 : 1 : 1 |
	// | Impossible :  N/A : 1 : 1 : 0 : 0 |
	// | Impossible :  N/A : 1 : 1 : 0 : 1 |
	// | Impossible :  N/A : 1 : 1 : 1 : 0 |
	// | 0xFE-0xFF  : 0xFF : 1 : 1 : 1 : 1 |
	//
	// Notably impossible:
	// b=0 && x=0 && y=0 && r=1  (Because (0x7F-0x00 == 0x7F) and (0x7F-0x7F == 0x00))
	// b=1 && x=0 && y=0 && r=0  (Because (0x00-0x7F == 0x81) and (0x00-0x01 == 0xFF))
	// b=0 && x=1 && y=1 && r=1  (Because (0xFF-0x80 == 0x7F) and (0xFF-0xFF == 0x00))
	// b=1 && x=1 && y=1 && r=0  (Because (0x80-0x81 == 0xFF) and (0x80-0xFF == 0x81))
	// b=0 && x=0 && y=1  (Because (x=0 && y=1) implies (x<y), which is _always_ overflow.)
	// b=1 && x=1 && y=0  (Because (x=1 && y=0) implies (x>y), which _never_ overflows.)
	// 
	// |            : res  :   :msb:msb:msb|
	// |  x  -  y   :  = r : b : x : y : r |
	// +------------+------+---+---+---+---+
	// | 0x01-0x01  : 0x00 : 0 : 0 : 0 : 0 |
	// | 0x7F-0x7F  : 0x00 : 0 : 0 : 0 : 0 |
	// | 0x80-0x7F  : 0x01 : 0 : 1 : 0 : 0 |
	// | 0xFF-0x01  : 0xFE : 0 : 1 : 0 : 1 |
	// | 0x80-0x80  : 0x00 : 0 : 1 : 1 : 0 |
	// | 0xFF-0x80  : 0x7F : 0 : 1 : 1 : 0 |
	// | 0xFF-0xFF  : 0x00 : 0 : 1 : 1 : 0 |
	// | 0x00-0x7F  : 0x81 : 1 : 0 : 0 : 1 |
	// | 0x00-0x01  : 0xFF : 1 : 0 : 0 : 1 |
	// | 0x01-0xFF  : 0x02 : 1 : 0 : 1 : 0 |
	// | 0x7E-0xFF  : 0x7F : 1 : 0 : 1 : 0 |
	// | 0x00-0x80  : 0x80 : 1 : 0 : 1 : 1 |
	// | 0x7F-0x80  : 0xFF : 1 : 0 : 1 : 1 |
	// | 0xFE-0xFF  : 0xFF : 1 : 1 : 1 : 1 |
	// | Impossible :  N/A : 0 : 0 : 0 : 1 |
	// | Impossible :  N/A : 0 : 0 : 1 : 0 |
	// | Impossible :  N/A : 0 : 0 : 1 : 1 |
	// | Impossible :  N/A : 0 : 1 : 1 : 1 |
	// | Impossible :  N/A : 1 : 0 : 0 : 0 |
	// | Impossible :  N/A : 1 : 1 : 0 : 0 |
	// | Impossible :  N/A : 1 : 1 : 0 : 1 |
	// | Impossible :  N/A : 1 : 1 : 1 : 0 |
	//
	// To wittle this down a bit, we get a boolean expression simplifier
	// (like the one at https://www.boolean-algebra.com/), and then enter
	// this expression:
	//
	// !((!X&!Y&!Z)|(X&!Y&!Z)|(X&!Y&Z)|(X&Y&!Z))
	// |((!X&!Y&Z)|(!X&Y&!Z)|(!X&Y&Z)|(X&Y&Z))
	//
	// Where X = msb(x); Y = msb(y); and Z = r = msb(res)
	// (For the given solver, you'll also need to put "+" instead of "|" and
	// remove all the &'s, because juxtaposition is the AND operator in
	// that site's syntax.)
	//
	// The above expression becomes TRUE when b should be 1,
	// and becomes FALSE when b should be 0.
	// So it accomplishes what we want: the expression predicts the carry
	// bit based on the values of msb(x), msb(y), and msb(r).
	//
	// However, the expression is very suboptimal for machine execution.
	// So the boolean expression simplifier will give us this instead:
	//
	// (Y&!X)|(Y&Z)|(Z&!X) => b = (!x & y)|(y & r)|(!x & r)
	//
	// Ah, much better!
	// 
	// But we can do a little better.
	// 
	// b = (!x & y)|(y & r)|(!x & r)
	// b = (!x & y)|(r&(y|!x))          // Distributive law: (a&b)|(a&c) == a&(b|c)
	// b = (y & !x)|(r & (y | !x))      // Commutative property of &
	// b = (y & !x)|(r & (!(!y) | !x))  // Involution law: !!a == a
	// b = (y & !x)|(r & !(!y & !(!x))) // Demorgan's law: !(a&b) == (!a | !b)
	// b = (y & !x)|(r & !(!y & x))     // Involution law: !!a == a
	// b = (y & !x)|(!(!r) & !(!y & x)) // Involution law: !!a == a
	// b = !(!(y & !x) & !(r & !(!y & x)))
	// But we have access to other operators, notably XOR.
	//
	// b = ((x^y^r)&(!y&!r))|(y|r)
	// b = ((x^y^r)&!!(!y&!r))|(y|r)
	// b = ((x^y^r)&!(!!y|!!r))|(y|r)
	// b = ((x^y^r)&!(y|r))|(y|r)
	// (Note: this is untrue! b != that expression)
	// (That expression equals (x|y|r), as proven below. But b != (x|y|r))
	//
	// b = ((x^y^r)&(!y&!r))|(y|r)
	// b = ((x^y^r)&(!!(!y&!r)))|(y|r)
	// b = ((x^y^r)&(!(y|r)))|(y|r)
	// b = ((x|y|r)^(y|y|r)^(r|y|r))|(y|r)
	// b = ((x|y|r)^(y|r)^(y|r))|(y|r)
	// b = ((x|y|r)^0)|(y|r)
	// b = (x|y|r)|(y|r)
	// b = (x|y|r)
	//
	//
	// b = (x&y&r)|(!x&(y|r))
	//
	// b = (x&y&r)^(x|y|r)^x
	// b = (!!(x&y&r))^(x|y|r)^x
	// b = (!(!x|!y|!r))^(x|y|r)^x
	// 
	// b = (x&y&r)^(x|y|r)^x
	// b = (x&y&r)^((x^y^r)&(!x))
	// b = (x^y^r)&(x^y^r)&(!x)
	// b = (x^y^r)&(!x)
	// TODO: This one seems wrong. I messed something up somewhere.
	//
0	0	0	F
0	0	1	T
0	1	0	T
0	1	1	T
1	0	0	F
1	0	1	F
1	1	0	F
1	1	1	T

| x : y : r : t : ^ :!(y&r):!(y^r): ^ :!x^!(y&r):|
|---+---+---+---+---+------+------+---:---------+|
| 0 : 0 : 0 : 0 : 0 :   1  :   1  : 0 :    0    :|
| 0 : 0 : 1 : 1 : 1 :   1  :   0  : 1 :    0    :|
| 0 : 1 : 0 : 1 : 1 :   1  :   0  : 1 :    0    :|
| 0 : 1 : 1 : 1 : 0 :   0  :   1  : 1 :    1    :|
| 1 : 0 : 0 : 0 : 1 :   1  :   1  : 0 :    1    :|
| 1 : 0 : 1 : 0 : 0 :   1  :   0  : 1 :    1    :|
| 1 : 1 : 0 : 0 : 0 :   1  :   0  : 1 :    1    :|
| 1 : 1 : 1 : 1 : 1 :   0  :   1  : 1 :    0    :|

| x : y : r : t :!x&y: <|r:x^r:y^r:y|r:(y^r)^(y|r):!x&(y|r): <| |
|---+---+---+---+----+----:---:---:---:-----------:--------:----|
| 0 : 0 : 0 : 0 :  0 :  0 : 0 : 0 : 0 :     0     :    0   :  0 |
| 0 : 0 : 1 : 1 :  0 :  1 : 1 : 1 : 1 :     0     :    1   :  1 |
| 0 : 1 : 0 : 1 :  1 :  1 : 0 : 1 : 1 :     0     :    1   :  1 |
| 0 : 1 : 1 : 1 :  1 :  1 : 1 : 0 : 1 :     1     :    1   :  1 |
| 1 : 0 : 0 : 0 :  0 :  0 : 1 : 0 : 0 :     0     :    0   :  0 |
| 1 : 0 : 1 : 0 :  0 :  1 : 0 : 1 : 1 :     0     :    0   :  0 |
| 1 : 1 : 0 : 0 :  0 :  0 : 1 : 1 : 1 :     0     :    0   :  0 |
| 1 : 1 : 1 : 1 :  0 :  1 : 0 : 0 : 1 :     1     :    0   :  1 |

	// First XOR-based solution?
	// b = ((y^r)^(y|r))|(!x&(y|r))
	//
	// b = ((y^r)^(y|r))|(!x&(y|r))
	// b = (y&r)|(!x&(y|r))
	// b = (y&r)|(!x&!!(y|r))
	// b = (y&r)|(!x&!(!y&!r))
	// 
	// 
	// 
	// b = (((y|r)&(!y|!r))^(y|r))|(!x&(y|r))
	// b = (((y|r)^(!y|!r))&(y|r))|(!x&(y|r))
	// 
	// 
	// b = (y^r^(y|r))|(!x&(y|r))
	// b = (y^(!r&(y&r)))|(!x&(y|r))
	// b = (y&(!r^(y&r)))|(!x&(y|r))
	// b = (y&(!r&(y^r)))|(!x&(y|r))
	// b = (y&!r&(y^r))|(!x&(y|r))

Xor properties:
a^b ≡ (a&!b)|(!a&b)
a^b ≡ (a|b)&(!a|!b)
a&(b^c) ≡ (a&b)^(a&c)
(!a)&(b^c) ≡ (a|b)^(a|c)
(a|b)^a ≡ (a^b)&(!a)   // Does this work in ternary?
(a&b)^a ≡ (a^b)&a
(a^b)^(a|b) ≡ a&b
(a|b)&(!a|!c) ≡ (a^b)^(a&(b^c))
(a|b)&(a|c) ≡ (!a^b^c)&(a|b|c)
a^(b|c) = (a)^(!b&c)^(a&c)

Other:
p|(q&r)≡(p|q)&(p|r)
p&(q|r)≡(p&q)|(p&r)


(a|b)&(a|c)
Let (a|b)=p and (a|c)=q
then
p&q = (p^q)^(p|q)
Substituting back..
(a|b)&(a|c)= ((a|b)^(a|c))^((a|b)|(a|c))
= (a|b)^(a|c)^(a|b|a|c)
= (a|b)^(a|c)^(a|b|c)
= (!a&(b^c))^(a|b|c)
= (!a^(b^c))&(a|b|c)
= (!a^b^c)&(a|b|c)


Rewrite (a&b)|(a&c) in terms of ^
p&(q|r)≡(p&q)|(p&r)
then
(a&b)|(a&c)=a&(b|c)
Let (b|c)=g
a&g = (a^g)^(a|g)
Subsituting...
a&(b|c) = (a^(b|c))^(a|(b|c))
=(a^(b|c))^(a|b|c)
=((a)^(!b&c)^(a&c))^(a|b|c)
=(a)^(!b&c)^(a&c)^(a|b|c)

	// b = (x&y&r)|(!x&(y|r))
	// b = (x&y&r)|(!x&!!(y|r))
	// b = (x&y&r)|(!x&!(!y&!r))

	// b = (!x & y)|(y & r)|(!x & r)
	// b = (!x & y)|

| a : b : c : !b :!c :!b|!c: & : b|c :!(b|c): ? :!? |
|---+---+---+----+---+-----+---+-----+------+---+---|
| 0 : 0 : 0 :  1 : 1 :  1  : 0 :  0  :   1  : 1 : 0 |
| 0 : 0 : 1 :  1 : 0 :  1  : 0 :  1  :   0  : 0 : 1 |
| 0 : 1 : 0 :  0 : 1 :  1  : 0 :  1  :   0  : 0 : 1 |
| 0 : 1 : 1 :  0 : 0 :  0  : 0 :  1  :   0  : 0 : 1 |
| 1 : 0 : 0 :  1 : 1 :  1  : 1 :  0  :   1  : 1 : 0 |
| 1 : 0 : 1 :  1 : 0 :  1  : 1 :  1  :   0  : 1 : 0 |
| 1 : 1 : 0 :  0 : 1 :  1  : 1 :  1  :   0  : 1 : 0 |
| 1 : 1 : 1 :  0 : 0 :  0  : 0 :  1  :   0  : 0 : 1 |


!((a&(!b|!c))|!(b|c))
!((a&!b)|(a&!c)|(b|c))


| a : b : c : !a : b|c : !a&(b|c) : (b^c) : (b&c) : | : !a|b|c : !(!a|b|c) : ((b^c)|(b&c))^!(!a|b|c)
|---+---+---+----+-----+----------+-------+-------+---:--------+-----------+----------------------
| 0 : 0 : 0 :  1 :  0  :     0    :   0   :   0   : 0 :    1   :      0    :         0
| 0 : 0 : 1 :  1 :  1  :     1    :   1   :   0   : 1 :    1   :      0    :         1
| 0 : 1 : 0 :  1 :  1  :     1    :   1   :   0   : 1 :    1   :      0    :         1
| 0 : 1 : 1 :  1 :  1  :     1    :   0   :   1   : 1 :    1   :      0    :         1
| 1 : 0 : 0 :  0 :  0  :     0    :   1   :   0   : 1 :    0   :      1    :         0
| 1 : 0 : 1 :  0 :  1  :     0    :   0   :   0   : 0 :    1   :      0    :         0
| 1 : 1 : 0 :  0 :  1  :     0    :   0   :   0   : 0 :    1   :      0    :         0
| 1 : 1 : 1 :  0 :  1  :     0    :   1   :   1   : 1 :    1   :      0    :         1


| !x : y : r : b : ^ : & : | : !y : !r : !&! : ^&& : y|r : <|< :
|----+---+---+---+---+---+---+----+----+-----+-----+-----+-----+
|  0 : 0 : 0 : F : 0 : 0 : 0 :  1 :  1 :  1  :  0  :  0  :  0  :  
|  0 : 0 : 1 : F : 1 : 0 : 1 :  1 :  0 :  0  :  0  :  1  :  1  :
|  0 : 1 : 0 : F : 1 : 0 : 1 :  0 :  1 :  0  :  0  :  1  :  1  :
|  0 : 1 : 1 : T : 0 : 0 : 1 :  0 :  0 :  0  :  0  :  1  :  1  :
|  1 : 0 : 0 : F : 1 : 0 : 1 :  1 :  1 :  1  :  1  :  0  :  1  :
|  1 : 0 : 1 : T : 0 : 0 : 1 :  1 :  0 :  0  :  0  :  1  :  1  :
|  1 : 1 : 0 : T : 0 : 0 : 1 :  0 :  1 :  0  :  0  :  1  :  1  :
|  1 : 1 : 1 : T : 1 : 1 : 1 :  0 :  0 :  0  :  0  :  1  :  1  :

| !x : !y : !r : b : ^ : & : | : ~| : '| :
|----+----+----+---+---+---+---+----+----+
|  0 :  1 :  1 : F : 0 : 0 : 1 :  0 :  1 :
|  0 :  1 :  0 : F : 1 : 0 : 1 :  0 :  1 :
|  0 :  0 :  1 : F : 1 : 0 : 1 :  0 :  1 :
|  0 :  0 :  0 : T : 0 : 0 : 0 :  1 :  1 :
|  1 :  1 :  1 : F : 1 : 1 : 1 :  0 :  0 :
|  1 :  1 :  0 : T : 0 : 0 : 1 :  0 :  1 :
|  1 :  0 :  1 : T : 0 : 0 : 1 :  0 :  1 :
|  1 :  0 :  0 : T : 1 : 0 : 1 :  0 :  1 :

| x : y : r : b : ^ : & : | : ~& :
|---+---+---+---+---+---+---+----+
| 1 : 0 : 0 : F : 1 : 0 : 1 :  1 :
| 1 : 0 : 1 : F : 0 : 0 : 1 :  1 :
| 1 : 1 : 0 : F : 0 : 0 : 1 :  1 :
| 1 : 1 : 1 : T : 1 : 1 : 1 :  0 :
| 0 : 0 : 0 : F : 0 : 0 : 0 :  1 :
| 0 : 0 : 1 : T : 1 : 0 : 1 :  1 :
| 0 : 1 : 0 : T : 1 : 0 : 1 :  1 :
| 0 : 1 : 1 : T : 0 : 0 : 1 :  1 :



(A AND !B) OR (!A AND B)
(A OR B) AND !(A AND B)
(A OR B) AND (!A OR !B)
| A : B : A&!B : !A&B : ^ : A|B : !(A&B) |
|---+---+------+------+---+-----+--------|
| 0 : 0 :   0  :   0  : 0 :  0  :    1   |
| 0 : 1 :   0  :   1  : 1 :  1  :    1   |
| 1 : 0 :   1  :   0  : 1 :  1  :    1   |
| 1 : 1 :   0  :   0  : 0 :  1  :    0   |


Does a^(b|c) == (a^b)|(a^c)
(No, it does not.)

| a : b : c : a^b : a^c : ^|^ : b|c : a^| |
|---+---+---+-----+-----+-----+-----+-----|
| 0 : 0 : 0 :  0  :  0  :  0  :  0  :  0  |
| 0 : 0 : 1 :  0  :  1  :  1  :  1  :  1  |
| 0 : 1 : 0 :  1  :  0  :  1  :  1  :  1  |
| 0 : 1 : 1 :  1  :  1  :  1  :  1  :  1  |
| 1 : 0 : 0 :  1  :  1  :  1  :  0  :  1  |
| 1 : 0 : 1 :  1  :  0  :  1  :  1  :  0  |
| 1 : 1 : 0 :  0  :  1  :  1  :  1  :  0  |
| 1 : 1 : 1 :  0  :  0  :  0  :  1  :  0  |


Does a^(b&c) == (a^b)&(a^c)
(No, it does not.)

| a : b : c : a^b : a^c : ^&^ : b&c : a^| |
|---+---+---+-----+-----+-----+-----+-----|
| 0 : 0 : 0 :  0  :  0  :  0  :  0  :  0  |
| 0 : 0 : 1 :  0  :  1  :  0  :  0  :  0  |
| 0 : 1 : 0 :  1  :  0  :  0  :  0  :  0  |
| 0 : 1 : 1 :  1  :  1  :  1  :  1  :  1  |
| 1 : 0 : 0 :  1  :  1  :  1  :  0  :  1  |
| 1 : 0 : 1 :  1  :  0  :  0  :  0  :  1  |
| 1 : 1 : 0 :  0  :  1  :  0  :  0  :  1  |
| 1 : 1 : 1 :  0  :  0  :  0  :  1  :  0  |

Does a&(b^c) == (a&b)^(a&c)
(It does!)

| a : b : c : a&b : a&c : &^& : b^c : a&^ |
|---+---+---+-----+-----+-----+-----+-----|
| 0 : 0 : 0 :  0  :  0  :  0  :  0  :  0  |
| 0 : 0 : 1 :  0  :  0  :  0  :  1  :  0  |
| 0 : 1 : 0 :  0  :  0  :  0  :  1  :  0  |
| 0 : 1 : 1 :  0  :  0  :  0  :  0  :  0  |
| 1 : 0 : 0 :  0  :  0  :  0  :  0  :  0  |
| 1 : 0 : 1 :  0  :  1  :  1  :  1  :  1  |
| 1 : 1 : 0 :  1  :  0  :  1  :  1  :  1  |
| 1 : 1 : 1 :  1  :  1  :  0  :  0  :  0  |

Does a|(b^c) == (a|b)^(a|c)
(No, it does not. But it makes an interesting pattern.)

| a : b : c : a|b : a|c : |^| : b^c : a|^ |
|---+---+---+-----+-----+-----+-----+-----|
| 0 : 0 : 0 :  0  :  0  :  0  :  0  :  0  |
| 0 : 0 : 1 :  0  :  1  :  1  :  1  :  1  |
| 0 : 1 : 0 :  1  :  0  :  1  :  1  :  1  |
| 0 : 1 : 1 :  1  :  1  :  0  :  0  :  0  |
| 1 : 0 : 0 :  1  :  1  :  0  :  0  :  1  |
| 1 : 0 : 1 :  1  :  1  :  0  :  1  :  1  |
| 1 : 1 : 0 :  1  :  1  :  0  :  1  :  1  |
| 1 : 1 : 1 :  1  :  1  :  0  :  0  :  1  |

Does (!a)&(b^c) == (a|b)^(a|c)
(It does!)

| a : b : c : a|b : a|c : |^| : b^c : !a&(b^c) |
|---+---+---+-----+-----+-----+-----+----------|
| 0 : 0 : 0 :  0  :  0  :  0  :  0  :     0    |
| 0 : 0 : 1 :  0  :  1  :  1  :  1  :     1    |
| 0 : 1 : 0 :  1  :  0  :  1  :  1  :     1    |
| 0 : 1 : 1 :  1  :  1  :  0  :  0  :     0    |
| 1 : 0 : 0 :  1  :  1  :  0  :  0  :     0    |
| 1 : 0 : 1 :  1  :  1  :  0  :  1  :     0    |
| 1 : 1 : 0 :  1  :  1  :  0  :  1  :     0    |
| 1 : 1 : 1 :  1  :  1  :  0  :  0  :     0    |


(a|b)^a = (a^b)&(!a)
(It does!)

| a : b : a|b : (a|b)^a  : a^b : (a^b)&!a |
|---+---+-----+----------+-----+----------|
| 0 : 0 :  0  :     0    :  0  :     0    |
| 0 : 1 :  1  :     1    :  1  :     1    |
| 1 : 0 :  1  :     0    :  1  :     0    |
| 1 : 1 :  1  :     0    :  0  :     0    |

(a&b)^a = (a^b)&a
(It does!)

| a : b : a&b : (a&b)^a : a^b : (a^b)&a |
|---+---+-----+---------+-----+---------|
| 0 : 0 :  0  :    0    :  0  :    0    |
| 0 : 1 :  0  :    0    :  1  :    0    |
| 1 : 0 :  0  :    1    :  1  :    1    |
| 1 : 1 :  1  :    0    :  0  :    0    |

Does (a&b)^c = (a^b)&c
No, it does not.

| a : b : c : a&b :(a&b)^c: a^b :(a^b)&c|
|---+---+---+-----+-------+-----+-------|
| 0 : 0 : 0 :  0  :   0   :  0  :   0   |
| 0 : 0 : 1 :  0  :   1   :  0  :   1   |
| 0 : 1 : 0 :  0  :   0   :  1  :   0   |
| 0 : 1 : 1 :  0  :   1   :  1  :   0   |
| 1 : 0 : 0 :  0  :   0   :  1  :   0   |
| 1 : 0 : 1 :  0  :   1   :  1  :   1   |
| 1 : 1 : 0 :  1  :   1   :  0  :   0   |
| 1 : 1 : 1 :  1  :   0   :  0  :   0   |

Does (a&b)^c = (a^c)|b
No, it does not. (but, close?)

| a : b : c : a&b :(a&b)^c: a^c :(a^c)|!b|
|---+---+---+-----+-------+-----+--------|
| 0 : 0 : 0 :  0  :   0   :  0  :    0   |
| 0 : 0 : 1 :  0  :   1   :  1  :    1   |
| 0 : 1 : 0 :  0  :   0   :  0  :    0   |
| 0 : 1 : 1 :  0  :   1   :  1  :    1   |
| 1 : 0 : 0 :  0  :   0   :  1  :    1   |
| 1 : 0 : 1 :  0  :   1   :  0  :    1   |
| 1 : 1 : 0 :  1  :   1   :  1  :    1   |
| 1 : 1 : 1 :  1  :   0   :  0  :    0   |

Does (a&b)^c = (a^c)^!b
No, it does not. (but, close?)

| a : b : c : a&b :(a&b)^c: a^c :(a^c)^!b|
|---+---+---+-----+-------+-----+--------|
| 0 : 0 : 0 :  0  :   0   :  0  :    1   |
| 0 : 0 : 1 :  0  :   1   :  1  :    0   |
| 0 : 1 : 0 :  0  :   0   :  0  :    0   |
| 0 : 1 : 1 :  0  :   1   :  1  :    1   |
| 1 : 0 : 0 :  0  :   0   :  1  :    0   |
| 1 : 0 : 1 :  0  :   1   :  0  :    1   |
| 1 : 1 : 0 :  1  :   1   :  1  :    1   |
| 1 : 1 : 1 :  1  :   0   :  0  :    0   |

Does !(a^b)^c = (a^c)^!b
It Does!

| a : b : c :!(a^b):!(a^b)^c: a^c :(a^c)^!b|
|---+---+---+------+--------+-----+--------|
| 0 : 0 : 0 :   1  :    1   :  0  :    1   |
| 0 : 0 : 1 :   1  :    0   :  1  :    0   |
| 0 : 1 : 0 :   0  :    0   :  0  :    0   |
| 0 : 1 : 1 :   0  :    1   :  1  :    1   |
| 1 : 0 : 0 :   0  :    0   :  1  :    0   |
| 1 : 0 : 1 :   0  :    1   :  0  :    1   |
| 1 : 1 : 0 :   1  :    1   :  1  :    1   |
| 1 : 1 : 1 :   1  :    0   :  0  :    0   |

(a^b)^(a|b) = a&b
It Does!

| a : b : a^b : a|b :(a^b)^(a|b): a&b |
|---+---+-----+-----+-----------+-----|
| 0 : 0 :  0  :  0  :     0     :  0  |
| 0 : 1 :  1  :  1  :     0     :  0  |
| 1 : 0 :  1  :  1  :     0     :  0  |
| 1 : 1 :  0  :  1  :     1     :  1  |


Does (a|b)&(!a|!c) == (a^b)^(a&(b^c))
Yes, it does.

| a : b : c :(a|b):(!a|!c): <&  :a^b:b^c:a&(b^c): <^  |
|---+---+---+-----+-------+-----+---+---+-------+-----|
| 0 : 0 : 0 :  0  :   1   :  0  : 0 : 0 :   0   :  0  |
| 0 : 0 : 1 :  0  :   1   :  0  : 0 : 1 :   0   :  0  |
| 0 : 1 : 0 :  1  :   1   :  1  : 1 : 1 :   0   :  1  |
| 0 : 1 : 1 :  1  :   1   :  1  : 1 : 0 :   0   :  1  |
| 1 : 0 : 0 :  1  :   1   :  1  : 1 : 0 :   0   :  1  |
| 1 : 0 : 1 :  1  :   0   :  0  : 1 : 1 :   1   :  0  |
| 1 : 1 : 0 :  1  :   1   :  1  : 0 : 1 :   1   :  1  |
| 1 : 1 : 1 :  1  :   0   :  0  : 0 : 0 :   0   :  0  |

Does (a|b)&(a|c) == (a^b)^(a&(b^c))

??????

| a : b : c :(a|b):(a|c): <&  :a^b:b^c:!(a^c): <^  |
|---+---+---+-----+-----+-----+---+---+------+-----|
| 0 : 0 : 0 :  0  :  0  :  0  : 0 : 0 :   1  :  0  |
| 0 : 0 : 1 :  0  :  1  :  0  : 0 : 1 :   0  :  0  |
| 0 : 1 : 0 :  1  :  0  :  0  : 1 : 1 :   1  :  1  |
| 0 : 1 : 1 :  1  :  1  :  1  : 1 : 0 :   0  :  1  |
| 1 : 0 : 0 :  1  :  1  :  1  : 1 : 0 :   0  :  1  |
| 1 : 0 : 1 :  1  :  1  :  1  : 1 : 1 :   1  :  0  |
| 1 : 1 : 0 :  1  :  1  :  1  : 0 : 1 :   0  :  1  |
| 1 : 1 : 1 :  1  :  1  :  1  : 0 : 0 :   1  :  0  |


a^(b|c) = ((a^b)|(b^c))^(a&(b^c))

(Whew, I'm not sure if that even helps, but it's a start I guess?)

| a : b : c :(b|c):a^(b|c):a^b:b^c:(a^b)|(b^c):a&(b^c): <^  |
|---+---+---+-----+-------+---+---+-----------+-------+-----|
| 0 : 0 : 0 :  0  :   0   : 0 : 0 :     0     :   0   :  0  |
| 0 : 0 : 1 :  1  :   1   : 0 : 1 :     1     :   0   :  1  |
| 0 : 1 : 0 :  1  :   1   : 1 : 1 :     1     :   0   :  1  |
| 0 : 1 : 1 :  1  :   1   : 1 : 0 :     1     :   0   :  1  |
| 1 : 0 : 0 :  0  :   1   : 1 : 0 :     1     :   0   :  1  |
| 1 : 0 : 1 :  1  :   0   : 1 : 1 :     1     :   1   :  0  |
| 1 : 1 : 0 :  1  :   0   : 0 : 1 :     1     :   1   :  0  |
| 1 : 1 : 1 :  1  :   0   : 0 : 0 :     0     :   0   :  0  |

By  (!a)&(b^c) ≡ (a|b)^(a|c)
We can reduce the above:
a^(b|c) = ((a^b)|(b^c))^(a&(b^c))
= ((b^a)|(b^c))^(a&(b^c))
= ((!b)&(a^c))^(a&(b^c))
= ((!b&a)^(!b&c))^((a&b)^(a&c))
= (!b&a)^(!b&c)^(a&b)^(a&c)
= (!b&a)^(a&b)^(!b&c)^(a&c)
= (a&(!b^b))^(!b&c)^(a&c)
= (a&1)^(!b&c)^(a&c)
= (a)^(!b&c)^(a&c)

a^(b|c) = (!b&a)^(!b&c)^(a&b)^(a&c)
a^(b|c) = (a)^(!b&c)^(a&c)
NOPE it didn't work.

| a : b : c :(!b|c):a^(!b|c):a&c: <^  :b|c:a^(b|c)|
|---+---+---+------+--------+---+-----+---+-------|
| 0 : 0 : 0 :   1  :    1   : 0 :  1  : 0 :   0   |
| 0 : 0 : 1 :   1  :    1   : 0 :  1  : 1 :   1   |
| 0 : 1 : 0 :   0  :    0   : 0 :  0  : 1 :   1   |
| 0 : 1 : 1 :   1  :    1   : 0 :  1  : 1 :   1   |
| 1 : 0 : 0 :   1  :    0   : 0 :  0  : 0 :   1   |
| 1 : 0 : 1 :   1  :    0   : 1 :  1  : 1 :   0   |
| 1 : 1 : 0 :   0  :    1   : 0 :  1  : 1 :   0   |
| 1 : 1 : 1 :   1  :    0   : 1 :  0  : 1 :   0   |


\overline{\left(\overline{X}\overline{Y}\overline{Z}+X\overline{Y}\overline{Z}+X\overline{y}Z+XY\overline{Z}\right)}+\left(\overline{X}\overline{Y}Z+\overline{X}Y\overline{Z}+\overline{X}YZ+XYZ\right)

\overline{X}\overline{Y}Z+\overline{X}Y\overline{Z}+\overline{X}YZ+XYZ+\overline{\left(\overline{X}\overline{Y}\overline{z}+X\overline{Y}\overline{Z}+X\overline{y}Z+XY\overline{Z}\right)}

	// 
	// |            : res  :            : res' :   :msb:msb:msb:   :msb|
	// |  x  -  y   :  = r :  y  -  x   :  =r' : b : x : y : r : b': r'|
	// +------------+------+------------+------+---+---+---+---+---+---+
	// | 0x01-0x01  : 0x00 : 0x01-0x01  : 0x00 : 0 : 0 : 0 : 0 : 0 : 0 |
	// | 0x7F-0x7F  : 0x00 : 0x7F-0x7F  : 0x00 : 0 : 0 : 0 : 0 : 0 : 0 |
	// | 0x80-0x7F  : 0x01 : 0x7F-0x80  : 0xFF : 0 : 1 : 0 : 0 : 1 : 1 |
	// | 0xFF-0x01  : 0xFE : 0x01-0xFF  : 0x02 : 0 : 1 : 0 : 1 : 0 : 0 |
	// | 0x80-0x80  : 0x00 : 0x80-0x80  : 0x00 : 0 : 1 : 1 : 0 : 0 : 0 |
	// | 0xFF-0x80  : 0x7F : 0x80-0xFF  : 0x81 : 0 : 1 : 1 : 0 : 1 : 1 |
	// | 0xFF-0xFF  : 0x00 : 0xFF-0xFF  : 0x00 : 0 : 1 : 1 : 0 : 0 : 0 |
	// | 0x00-0x7F  : 0x81 : 0x7F-0x00  : 0x7F : 1 : 0 : 0 : 1 : 0 : 0 |
	// | 0x00-0x01  : 0xFF : 0x01-0x00  : 0x01 : 1 : 0 : 0 : 1 : 0 : 0 |
	// | 0x01-0xFF  : 0x02 : 0xFF-0x01  : 0xFE : 1 : 0 : 1 : 0 : 0 : 1 |
	// | 0x7E-0xFF  : 0x7F : 0xFF-0x7E  : 0x81 : 1 : 0 : 1 : 0 : 0 : 1 |
	// | 0x00-0x80  : 0x80 : 0x80-0x00  : 0x80 : 1 : 0 : 1 : 1 : 0 : 1 |
	// | 0x7F-0x80  : 0xFF : 0x80-0x7F  : 0x01 : 1 : 0 : 1 : 1 : 0 : 0 |
	// | 0xFE-0xFF  : 0xFF : 0xFF-0xFE  : 0x91 : 1 : 1 : 1 : 1 : 0 : 1 |
	// | Impossible :  N/A : Impossible :  N/A : 0 : 0 : 0 : 1 : ? : 1 |
	// | Impossible :  N/A : Impossible :  N/A : 0 : 0 : 1 : 0 : ? : 0 |
	// | Impossible :  N/A : Impossible :  N/A : 0 : 0 : 1 : 1 : ? : 1 |
	// | Impossible :  N/A : Impossible :  N/A : 0 : 1 : 1 : 1 : ? : 1 |
	// | Impossible :  N/A : Impossible :  N/A : 1 : 0 : 0 : 0 : ? : 0 |
	// | Impossible :  N/A : Impossible :  N/A : 1 : 1 : 0 : 0 : ? : 0 |
	// | Impossible :  N/A : Impossible :  N/A : 1 : 1 : 0 : 1 : ? : 1 |
	// | Impossible :  N/A : Impossible :  N/A : 1 : 1 : 1 : 0 : ? : 0 |
	//
	// | xx : yy : x-y : y-x : b : d : x : y : p : q :
	// |----+----+-----+-----+---+---+---+---+---+---+
	// | 00 : 00 :  00 :  00 : 0 : 0 : 0 : 0 : 0 : 0 : 
	// | 00 : 01 :  11 :  01 : 1 : 0 : 0 : 0 : 1 : 0 :
	// | 00 : 10 :  10 :  10 : 1 : 0 : 0 : 1 : 1 : 1 :
	// | 00 : 11 :  01 :  11 : 1 : 0 : 0 : 1 : 0 : 1 :
	// | 01 : 00 :  01 :  11 : 0 : 1 : 0 : 0 : 0 : 1 :
	// | 01 : 01 :  00 :  00 : 0 : 0 : 0 : 0 : 0 : 0 :
	// | 01 : 10 :  11 :  01 : 1 : 0 : 0 : 1 : 1 : 0 :
	// | 01 : 11 :  10 :  10 : 1 : 0 : 0 : 1 : 1 : 1 :
	// | 10 : 00 :  10 :  10 : 0 : 1 : 1 : 0 : 1 : 1 :
	// | 10 : 01 :  01 :  11 : 0 : 1 : 1 : 0 : 0 : 1 :
	// | 10 : 10 :  00 :  00 : 0 : 0 : 1 : 1 : 0 : 0 :
	// | 10 : 11 :  11 :  01 : 1 : 0 : 1 : 1 : 1 : 0 :
	// | 11 : 00 :  11 :  01 : 0 : 1 : 1 : 0 : 1 : 0 :
	// | 11 : 01 :  10 :  10 : 0 : 1 : 1 : 0 : 1 : 1 :
	// | 11 : 10 :  01 :  11 : 0 : 1 : 1 : 1 : 0 : 1 :
	// | 11 : 11 :  00 :  00 : 0 : 0 : 1 : 1 : 0 : 0 :
	//
	// (p&(x^y'))|!(x&!y')
	// (p&(x^y'))|(!x|y')
	//
	// | xx : yy : x-y : y-x : b : d : x : y : p : q : ^ : & : | :
	// |----+----+-----+-----+---+---+---+---+---+---+---+---+---+
	// | 00 : 00 :  00 :  00 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 :
	// | 01 : 01 :  00 :  00 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 :
	// | 10 : 10 :  00 :  00 : 0 : 0 : 1 : 1 : 0 : 0 : 0 : 0 : 1 :
	// | 11 : 11 :  00 :  00 : 0 : 0 : 1 : 1 : 0 : 0 : 0 : 0 : 1 :
	// | 01 : 00 :  01 :  11 : 0 : 1 : 0 : 0 : 0 : 1 : 1 : 0 : 1 :
	// | 10 : 01 :  01 :  11 : 0 : 1 : 1 : 0 : 0 : 1 : 0 : 0 : 1 :
	// | 10 : 00 :  10 :  10 : 0 : 1 : 1 : 0 : 1 : 1 : 0 : 0 : 1 :
	// | 11 : 01 :  10 :  10 : 0 : 1 : 1 : 0 : 1 : 1 : 0 : 0 : 1 :
	// | 11 : 00 :  11 :  01 : 0 : 1 : 1 : 0 : 1 : 0 : 0 : 0 : 1 :
	// | 11 : 10 :  01 :  11 : 0 : 1 : 1 : 1 : 0 : 1 : 1 : 0 : 1 :
	// | 00 : 01 :  11 :  01 : 1 : 0 : 0 : 0 : 1 : 0 : 1 : 0 : 1 :
	// | 00 : 11 :  01 :  11 : 1 : 0 : 0 : 1 : 0 : 1 : 1 : 0 : 1 :
	// | 01 : 10 :  11 :  01 : 1 : 0 : 0 : 1 : 1 : 0 : 1 : 0 : 1 :
	// | 00 : 10 :  10 :  10 : 1 : 0 : 0 : 1 : 1 : 1 : 1 : 0 : 1 :
	// | 01 : 11 :  10 :  10 : 1 : 0 : 0 : 1 : 1 : 1 : 1 : 0 : 1 :
	// | 10 : 11 :  11 :  01 : 1 : 0 : 1 : 1 : 1 : 0 : 0 : 1 : 1 :
	//
	// !(XYPQ+XYpq+XYPq+xYPq+xYpq+xYpQ+xyPq)
	// +(XYpQ+XyPq+XypQ+Xypq+xypQ)
	//
	// | xx : yy :~xx : ~yy : x-y : x+y : x~y : ~x-y : b : d :~y : x : y : p : q : q': ^
	// |----+----+----+-----+-----+-----+-----+------+---+---+---+---+---+---+---+---+---
	// | 00 : 00 : 11 :  11 :  00 :  00 :  01 :  11  : 0 : 1 : 1 : 0 : 0 : 0 : 0 : 1 : 0
	// | 01 : 01 : 10 :  10 :  00 :  10 :  11 :  01  : 0 : 1 : 1 : 0 : 0 : 0 : 1 : 0 : 1
	// | 01 : 00 : 10 :  11 :  01 :  01 :  10 :  10  : 0 : 1 : 1 : 0 : 0 : 0 : 1 : 1 : 1
	// | 10 : 01 : 01 :  10 :  01 :  11 :  00 :  00  : 0 : 0 : 1 : 1 : 0 : 0 : 0 : 0 : 1
	// | 10 : 00 : 01 :  11 :  10 :  10 :  11 :  01  : 0 : 1 : 1 : 1 : 0 : 1 : 1 : 0 : 1
	// | 11 : 01 : 00 :  10 :  10 :  00 :  01 :  11  : 0 : 0 : 1 : 1 : 0 : 1 : 0 : 1 : 0
	// | 11 : 00 : 00 :  11 :  11 :  11 :  00 :  00  : 0 : 0 : 1 : 1 : 0 : 1 : 0 : 0 : 0
	// | 10 : 10 : 01 :  01 :  00 :  00 :  01 :  11  : 0 : 0 : 0 : 1 : 1 : 0 : 0 : 1 : 0
	// | 11 : 11 : 00 :  00 :  00 :  10 :  11 :  01  : 0 : 0 : 0 : 1 : 1 : 0 : 1 : 0 : 1
	// | 11 : 10 : 00 :  01 :  01 :  01 :  10 :  10  : 0 : 0 : 0 : 1 : 1 : 0 : 1 : 1 : 1
	// | 00 : 01 : 11 :  10 :  11 :  01 :  10 :  10  : 1 : 1 : 1 : 0 : 0 : 1 : 1 : 1 : 0
	// | 00 : 11 : 11 :  00 :  01 :  11 :  00 :  00  : 1 : 0 : 0 : 0 : 1 : 0 : 0 : 0 : 1
	// | 01 : 10 : 10 :  01 :  11 :  11 :  00 :  00  : 1 : 0 : 0 : 0 : 1 : 1 : 0 : 0 : 0
	// | 00 : 10 : 11 :  01 :  10 :  10 :  11 :  01  : 1 : 1 : 0 : 0 : 1 : 1 : 1 : 0 : 1
	// | 01 : 11 : 10 :  00 :  10 :  00 :  01 :  11  : 1 : 0 : 0 : 0 : 1 : 1 : 0 : 1 : 0
	// | 10 : 11 : 01 :  00 :  11 :  01 :  10 :  10  : 1 : 0 : 0 : 1 : 1 : 1 : 1 : 1 : 0
	//
	//
	// | xx : yy : x|y : x^y : x&y : |-& : &-| : |-^ : b : q':q'': q : x : y : p : ^
	// |----+----+-----+-----+-----+-----+-----+-----+---+---+---+---+---+---+---+---
	// | 00 : 00 :  00 :  00 :  00 :  00 :  00 :  00 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0
	// | 01 : 01 :  01 :  00 :  01 :  00 :  00 :  01 : 0 : 0 : 0 : 1 : 0 : 0 : 0 : 1
	// | 01 : 00 :  10 :  01 :  00 :  10 :  10 :  01 : 0 : 1 : 1 : 1 : 0 : 0 : 0 : 1
	// | 10 : 01 :  11 :  11 :  00 :  11 :  01 :  00 : 0 : 1 : 0 : 0 : 1 : 0 : 0 : 1
	// | 10 : 00 :  10 :  10 :  00 :  10 :  10 :  00 : 0 : 1 : 1 : 1 : 1 : 0 : 1 : 1
	// | 11 : 01 :  11 :  10 :  01 :  10 :  10 :  01 : 0 : 1 : 1 : 0 : 1 : 0 : 1 : 0
	// | 11 : 00 :  11 :  11 :  00 :  11 :  01 :  00 : 0 : 1 : 0 : 0 : 1 : 0 : 1 : 0
	// | 10 : 10 :  10 :  00 :  10 :  00 :  00 :  10 : 0 : 0 : 0 : 0 : 1 : 1 : 0 : 0
	// | 11 : 11 :  11 :  00 :  11 :  00 :  00 :  11 : 0 : 0 : 0 : 1 : 1 : 1 : 0 : 1
	// | 11 : 10 :  11 :  01 :  10 :  01 :  11 :  10 : 0 : 0 : 1 : 1 : 1 : 1 : 0 : 1
	// | 00 : 01 :  01 :  01 :  00 :  01 :  11 :  00 : 1 : 0 : 1 : 1 : 0 : 0 : 1 : 0
	// | 00 : 11 :  11 :  11 :  00 :  11 :  01 :  00 : 1 : 1 : 0 : 0 : 0 : 1 : 0 : 1
	// | 01 : 10 :  11 :  11 :  00 :  11 :  01 :  00 : 1 : 1 : 0 : 0 : 0 : 1 : 1 : 0
	// | 00 : 10 :  10 :  10 :  00 :  10 :  10 :  00 : 1 : 1 : 1 : 1 : 0 : 1 : 1 : 1
	// | 01 : 11 :  11 :  10 :  01 :  10 :  10 :  01 : 1 : 1 : 1 : 0 : 0 : 1 : 1 : 0
	// | 10 : 11 :  11 :  01 :  10 :  01 :  11 :  10 : 1 : 0 : 1 : 1 : 1 : 1 : 1 : 0
	//
	//
	// | xx : yy : x-y : x|1 :x'-y : x|2 :x'-y : r+1 : r+2 : b : d : x :!x : y : p :!x|p:!x|y:(!x|p)&(!x|y):|1+1:|2+1:r+1:r+2:
	// |----+----+-----+-----+-----+-----+-----+-----+-----+---+---+---+---+---+---+----+----+-------------+----+----+---+---+---
	// | 00 : 00 :  00 :  01 :  01 :  10 :  10 :  01 :  10 : 0 : 0 : 0 : 1 : 0 : 0 :  1 :  1 :      1      :  0 :  1 : 0 : 1 :
	// | 01 : 01 :  00 :  01 :  00 :  11 :  10 :  01 :  10 : 0 : 0 : 0 : 1 : 0 : 0 :  1 :  1 :      1      :  0 :  1 : 0 : 1 :
	// | 10 : 10 :  00 :  11 :  01 :  10 :  00 :  01 :  10 : 0 : 0 : 1 : 0 : 1 : 0 :  0 :  1 :      0      :  0 :  0 : 0 : 1 :
	// | 11 : 11 :  00 :  11 :  00 :  11 :  00 :  01 :  10 : 0 : 0 : 1 : 0 : 1 : 0 :  0 :  1 :      0      :  0 :  0 : 0 : 1 :
	// | 01 : 00 :  01 :  01 :  01 :  11 :  11 :  10 :  11 : 0 : 1 : 0 : 1 : 0 : 0 :  1 :  1 :      1      :  0 :  1 : 1 : 1 :
	// | 10 : 01 :  01 :  11 :  10 :  10 :  01 :  10 :  11 : 0 : 1 : 1 : 0 : 0 : 0 :  0 :  0 :      0      :  1 :  0 : 1 : 1 :
	// | 10 : 00 :  10 :  11 :  11 :  10 :  10 :  11 :  00 : 0 : 1 : 1 : 0 : 0 : 1 :  1 :  0 :      0      :  1 :  1 : 1 : 0 :
	// | 11 : 01 :  10 :  11 :  10 :  11 :  10 :  11 :  00 : 0 : 1 : 1 : 0 : 0 : 1 :  1 :  0 :      0      :  1 :  1 : 1 : 0 :
	// | 11 : 00 :  11 :  11 :  11 :  11 :  11 :  00 :  01 : 0 : 1 : 1 : 0 : 0 : 1 :  1 :  0 :      0      :  1 :  1 : 0 : 0 :
	// | 11 : 10 :  01 :  11 :  01 :  11 :  01 :  10 :  11 : 0 : 1 : 1 : 0 : 1 : 0 :  0 :  1 :      0      :  0 :  0 : 1 : 1 :
	// | 00 : 01 :  11 :  01 :  00 :  10 :  01 :  00 :  01 : 1 : 0 : 0 : 1 : 0 : 1 :  1 :  1 :      1      :  0 :  0 : 0 : 0 :
	// | 00 : 11 :  01 :  01 :  10 :  10 :  11 :  10 :  11 : 1 : 0 : 0 : 1 : 1 : 0 :  1 :  1 :      1      :  1 :  1 : 1 : 1 :
	// | 01 : 10 :  11 :  01 :  11 :  11 :  01 :  00 :  01 : 1 : 0 : 0 : 1 : 1 : 1 :  1 :  1 :      1      :  1 :  0 : 0 : 0 :
	// | 00 : 10 :  10 :  01 :  11 :  10 :  00 :  11 :  00 : 1 : 0 : 0 : 1 : 1 : 1 :  1 :  1 :      1      :  1 :  0 : 1 : 0 :
	// | 01 : 11 :  10 :  01 :  10 :  11 :  00 :  11 :  00 : 1 : 0 : 0 : 1 : 1 : 1 :  1 :  1 :      1      :  1 :  0 : 1 : 0 :
	// | 10 : 11 :  11 :  11 :  00 :  10 :  11 :  00 :  01 : 1 : 0 : 1 : 0 : 1 : 1 :  1 :  1 :      1      :  0 :  1 : 0 : 0 :
	//
	//
	// | xx : yy :x|1 :y&2 :x'-y':x|1 :~(y&2):x'-y'': x-y :x-y': b : d : x :!x : y : p : '
	// |----+----+----+----+-----+----+------+-----+-----+----+---+---+---+---+---+---+---
	// | 00 : 00 : 01 : 00 :  01 : 01 :   11 :  10 :  00 : 00 : 0 : 0 : 0 : 1 : 0 : 0 : 0
	// | 01 : 01 : 01 : 00 :  01 : 01 :   11 :  10 :  00 : 01 : 0 : 0 : 0 : 1 : 0 : 0 : 0
	// | 10 : 10 : 11 : 10 :  01 : 11 :   01 :  10 :  00 : 00 : 0 : 0 : 1 : 0 : 1 : 0 : 0
	// | 11 : 11 : 11 : 10 :  01 : 11 :   01 :  10 :  00 : 01 : 0 : 0 : 1 : 0 : 1 : 0 : 0
	// | 01 : 00 : 01 : 00 :  01 : 01 :   11 :  10 :  01 : 01 : 0 : 1 : 0 : 1 : 0 : 0 : 0
	// | 10 : 01 : 11 : 00 :  11 : 11 :   11 :  00 :  01 : 10 : 0 : 1 : 1 : 0 : 0 : 0 : 1
	// | 10 : 00 : 11 : 00 :  11 : 11 :   11 :  00 :  10 : 10 : 0 : 1 : 1 : 0 : 0 : 1 : 1
	// | 11 : 01 : 11 : 00 :  11 : 11 :   11 :  00 :  10 : 11 : 0 : 1 : 1 : 0 : 0 : 1 : 1
	// | 11 : 00 : 11 : 00 :  11 : 11 :   11 :  00 :  11 : 11 : 0 : 1 : 1 : 0 : 0 : 1 : 1
	// | 11 : 10 : 11 : 10 :  01 : 11 :   01 :  10 :  01 : 01 : 0 : 1 : 1 : 0 : 1 : 0 : 0
	// | 00 : 01 : 01 : 00 :  01 : 01 :   11 :  10 :  11 : 00 : 1 : 0 : 0 : 1 : 0 : 1 : 0
	// | 00 : 11 : 01 : 10 :  11 : 01 :   01 :  00 :  01 : 10 : 1 : 0 : 0 : 1 : 1 : 0 : 1
	// | 01 : 10 : 01 : 10 :  11 : 01 :   01 :  00 :  11 : 11 : 1 : 0 : 0 : 1 : 1 : 1 : 1
	// | 00 : 10 : 01 : 10 :  11 : 01 :   01 :  00 :  10 : 10 : 1 : 0 : 0 : 1 : 1 : 1 : 1
	// | 01 : 11 : 01 : 10 :  11 : 01 :   01 :  00 :  10 : 11 : 1 : 0 : 0 : 1 : 1 : 1 : 1
	// | 10 : 11 : 11 : 10 :  01 : 11 :   01 :  10 :  11 : 00 : 1 : 0 : 1 : 0 : 1 : 1 : 0
	//
	//
	// | xx : yy : x&1: y&1: x-y :x'-y': b : d :!x : x : y : p : ' :p&':!x&p:!x|':
	// |----+----+----+----+-----+-----+---+---+---+---+---+---+---+---+----+----+
	// | 00 : 00 : 00 : 00 :  00 :  00 : 0 : 0 : 1 : 0 : 0 : 0 : 0 : 0 :  0 :  1 : 0
	// | 01 : 01 : 01 : 01 :  00 :  00 : 0 : 0 : 1 : 0 : 0 : 0 : 0 : 0 :  0 :  1 : 0
	// | 10 : 10 : 00 : 00 :  00 :  00 : 0 : 0 : 0 : 1 : 1 : 0 : 0 : 0 :  0 :  0 : 0
	// | 11 : 11 : 01 : 01 :  00 :  00 : 0 : 0 : 0 : 1 : 1 : 0 : 0 : 0 :  0 :  0 : 0
	// | 01 : 00 : 01 : 00 :  01 :  01 : 0 : 1 : 1 : 0 : 0 : 0 : 0 : 0 :  0 :  1 : 0
	// | 10 : 01 : 00 : 01 :  01 :  11 : 0 : 1 : 0 : 1 : 0 : 0 : 1 : 0 :  0 :  1 : 0
	// | 10 : 00 : 00 : 00 :  10 :  00 : 0 : 1 : 0 : 1 : 0 : 1 : 0 : 0 :  0 :  0 : 0
	// | 11 : 01 : 01 : 01 :  10 :  00 : 0 : 1 : 0 : 1 : 0 : 1 : 0 : 0 :  0 :  0 : 0
	// | 11 : 00 : 01 : 00 :  11 :  01 : 0 : 1 : 0 : 1 : 0 : 1 : 0 : 0 :  0 :  0 : 0
	// | 11 : 10 : 01 : 00 :  01 :  01 : 0 : 1 : 0 : 1 : 1 : 0 : 0 : 0 :  0 :  0 : 0
	// | 00 : 01 : 00 : 01 :  11 :  11 : 1 : 0 : 1 : 0 : 0 : 1 : 1 : 1 :  1 :  1 : 0
	// | 00 : 11 : 00 : 01 :  01 :  11 : 1 : 0 : 1 : 0 : 1 : 0 : 1 : 0 :  0 :  1 : 0
	// | 01 : 10 : 01 : 00 :  11 :  01 : 1 : 0 : 1 : 0 : 1 : 1 : 0 : 0 :  1 :  1 : 0
	// | 00 : 10 : 00 : 00 :  10 :  00 : 1 : 0 : 1 : 0 : 1 : 1 : 0 : 0 :  1 :  1 : 0
	// | 01 : 11 : 01 : 01 :  10 :  00 : 1 : 0 : 1 : 0 : 1 : 1 : 0 : 0 :  1 :  1 : 0
	// | 10 : 11 : 00 : 01 :  11 :  11 : 1 : 0 : 0 : 1 : 1 : 1 : 1 : 1 :  0 :  1 : 0
+/
	import std.traits : Signed;
	alias ST = Signed!T;

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

/+
	q2 += q1 >>> (n_bits/2);
	kmwriteln!("q2 += q1 >>> (n_bits/2);");
	kmwritefln!("q2.1    == %04X")(q2);
	q1 &= lo_mask;
	kmwriteln!("q1 &= lo_mask;");
	kmwritefln!("q1.4    == %04X")(q1);
	q1 += q0 >>> (n_bits/2);
	kmwriteln!("q1 += q0 >>> (n_bits/2);");
	kmwritefln!("q1.5    == %04X")(q1);
	q0 &= lo_mask;
	kmwriteln!("q0 &= lo_mask;");
	kmwritefln!("q0.1    == %04X")(q0);

	q2 += oflow << (n_bits/2);
	kmwriteln!("q2 += oflow << (n_bits/2)");
	kmwritefln!("q2.2    == %04X")(q2);

	q2 += q1 >>> (n_bits/2); // Propagate any overflow from the `q1 += q0[hi]` operation.
	kmwriteln!("q2 += q1 >>> (n_bits/2)");
	kmwritefln!("q2.3    == %04X")(q2);

	q0 |= q1 << (n_bits/2);
	kmwriteln!("q0 += q1 << (n_bits/2)");
	
	kmwriteln!("");
	kmwritefln!("q0.2    == %04X")(q0);
	kmwritefln!("q2.3    == %04X")(q2);
	kmwriteln!("");
/+
	T q0_over;
	T q1_over;
/+
	//q1_over = (lhs_sum >>> (n_bits-1)) | (rhs_sum >>> (n_bits-1));
	// or, by distributive property,
	//q1_over = (lhs_sum | rhs_sum) >>> (n_bits-1)
	q1_over = lhs_sum;
	q1_over |= rhs_sum;
	q1_over >>>= (n_bits-1);
+/

	// result = q2*m^2 + q1*m + q0
	// So we're almost there... but now we have to do those additions
	// while being careful about handling overflow.

	q0_over = q0 >>> (n_bits/2);
	q0 &= lo_mask;

	q1 += q0_over;
	q1_over += q1 >>> (n_bits/2);
	q1 <<= (n_bits/2);

	KaratsubMultiplyResult!T  result;

	result.lo = cast(T)(q0 | q1);
	result.hi = cast(T)(q2 + q1_over);
+/
+/
	KaratsubMultiplyResult!T  result;
	result.lo = q0;
	result.hi = q2;

	kmwritefln!("result.lo == %04X")(result.lo);
	kmwritefln!("result.hi == %04X")(result.hi);
	kmwritefln!("Finished `mult_karatsuba_full(lhs:%04X, rhs:%04X)`")(lhs, rhs);

	return result;
}

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

/+
	// |  a :  b : msb :  lhs  :  rhs  :   l*r   : a?b |
    // +----+----+-----+-------+-------+---------+-----+
    // | 00 : 00 :  0  : 0x07F : 0x07F : 0x03F01 :  00 |
    // | 00 : 00 :  1  :  N/A  :  N/A  :   N/A   :  00 | <- won't happen
    // | 00 : 01 :  0  : 0x07F : 0x0FF : 0x07E81 :  00 |
    // | 00 : 01 :  1  :  N/A  :  N/A  :   N/A   :  00 | <- won't happen
    // | 00 : 10 :  1  : 0x07F : 0x17F : 0x0BE01 :  00 |
    // | 00 : 11 :  1  : 0x07F : 0x1FF : 0x0FD81 :  00 |
    // | 01 : 00 :  0  : 0x0FF : 0x07F : 0x07E81 :  00 |
    // | 01 : 00 :  1  :  N/A  :  N/A  :   N/A   :  00 | <- won't happen
    // | 01 : 01 :  1  : 0x0FF : 0x0FF : 0x0FE01 :  00 |
    // | 01 : 10 :  1  : 0x0FF : 0x101 : 0x0FFFF :  00 |
    // | 01 : 10 :  0  : 0x0FF : 0x102 : 0x100FE :  01 |
    // | 01 : 10 :  0  : 0x0FF : 0x17F : 0x17D81 :  01 |
    // | 01 : 11 :  1  : 0x080 : 0x180 : 0x0C000 :  00 |
    // | 01 : 11 :  1  : 0x09F : 0x180 : 0x0EE80 :  00 | <- Hidden bit dependencies
    // | 01 : 11 :  0  : 0x0AF : 0x180 : 0x10680 :  01 |
    // | 01 : 11 :  1  : 0x0FF : 0x1FF : 0x1FD01 :  01 | <- ditto
    // | 10 : 00 :  0  : 0x17F : 0x07F : 0x0BE01 :  00 |
    // | 10 : 01 :  0  : 0x17F : 0x0FF : 0x17D81 :  01 |
    // | 10 : 10 :  0  : 0x17F : 0x17F : 0x23D01 :  10 |
    // | 10 : 11 :  0  : 0x17F : 0x1FF : 0x2FC81 :  10 |
    // | 11 : 00 :  0  : 0x1FF : 0x07F : 0x0FD81 :  00 |
    // | 11 : 01 :  0  : 0x1FF : 0x0FF : 0x1FD01 :  01 |
    // | 11 : 10 :  0  : 0x1FF : 0x17F : 0x2FC81 :  10 |
    // | 11 : 11 :  0  : 0x1FF : 0x1FF : 0x3FC01 :  11 |
    // 
    // Using commutative property of multiplication, we can reduce the table a bit:
	// |  a :  b :  lhs  :  rhs  :   l*r   : a?b |
    // +----+----+-------+-------+---------+-----+
    // | 00 : 00 : 0x07F : 0x07F : 0x03F01 :  00 |
    // | 00 : 01 : 0x07F : 0x0FF : 0x07E81 :  00 |
    // | 00 : 10 : 0x07F : 0x17F : 0x0BE01 :  00 |
    // | 00 : 11 : 0x07F : 0x1FF : 0x0FD81 :  00 |
    // | 01 : 01 : 0x0FF : 0x0FF : 0x0FE01 :  00 |
    // | 01 : 10 : 0x0FF : 0x17F : 0x17D81 :  01 |
    // | 01 : 11 : 0x0FF : 0x1FF : 0x1FD01 :  01 |
    // | 10 : 10 : 0x17F : 0x17F : 0x23D01 :  10 |
    // | 10 : 11 : 0x17F : 0x1FF : 0x2FC81 :  10 |
    // | 11 : 11 : 0x1FF : 0x1FF : 0x3FC01 :  11 |
+/
/+
	ubyte[16] expecteds =
		[0b00,0b00,0b00,0b00
		,0b00,0b00,0b01,0b01
		,0b00,0b01,0b10,0b10
		,0b00,0b01,0b10,0b11];

    ubyte test_op(ubyte l, ubyte r) {
		return cast(ubyte)(l*r);
    }

    //ubyte do_test(ubyte l, ubyte r) {
    void do_test(ubyte index) {
		//ubyte index = cast(ubyte)((l << 2) | r);
		ubyte expect = expecteds[index];
		ubyte l = cast(ubyte)(index >> 2);
		ubyte r = cast(ubyte)(index & 3);
		writefln("test_op(%02b,%02b) == %04b; expect %02b", l, r, test_op(l,r), expect);
    }

    for ( ubyte i = 0; i < 16; i++ )
		do_test(i);
+/

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

	writeln("unittest mult_karatsuba: done");
}
