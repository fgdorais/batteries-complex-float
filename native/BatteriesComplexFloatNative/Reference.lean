/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat

/-!
# Higher-precision reference values

For measuring accuracy: `ComplexFloat.Native.ref` computes a function with the C library's
`long double complex` functions (a 64-bit significand on x86-64, 11 bits more than `Float`), and
`ComplexFloat32.Native.ref` computes it with the `double complex` functions (29 bits more than
`Float32`). Functions are numbered as in `RefFn`.
-/

/-- The functions that have reference values, in the order of the C code. -/
public inductive RefFn where
  | exp | log | sqrt | sin | cos | tan | sinh | cosh | tanh
  | asin | acos | atan | asinh | acosh | atanh | abs | arg
deriving Repr, BEq, Inhabited

namespace RefFn

/-- The number of the function in the C code. -/
public def code : RefFn → UInt32
  | exp => 0 | log => 1 | sqrt => 2 | sin => 3 | cos => 4 | tan => 5 | sinh => 6
  | cosh => 7 | tanh => 8 | asin => 9 | acos => 10 | atan => 11 | asinh => 12
  | acosh => 13 | atanh => 14 | abs => 15 | arg => 16

/-- All of them. -/
public def all : List RefFn :=
  [exp, log, sqrt, sin, cos, tan, sinh, cosh, tanh, asin, acos, atan, asinh, acosh, atanh,
    abs, arg]

/-- The name of the function. -/
public def name (f : RefFn) : String := (reprStr f).drop 6 |>.toString

end RefFn

/-- A value `hi + lo` with more precision than `hi` alone: `hi` is the rounding and `lo` the
remainder, in each part. -/
public structure ComplexFloat.Native.Ref where
  /-- The rounded real part. -/
  hiRe : Float
  /-- The rounded imaginary part. -/
  hiIm : Float
  /-- The remainder of the real part. -/
  loRe : Float
  /-- The remainder of the imaginary part. -/
  loIm : Float
deriving Inhabited

@[extern "lean_complex_float_ref"]
opaque ComplexFloat.Native.refRaw (op : UInt32) : @& ComplexFloat → ComplexFloat.Native.Ref

/-- `f z` computed in `long double` precision. -/
public def ComplexFloat.Native.ref (f : RefFn) (z : ComplexFloat) : ComplexFloat.Native.Ref :=
  refRaw f.code z

@[extern "lean_complex_float32_ref"]
opaque ComplexFloat32.Native.refRaw (op : UInt32) : @& ComplexFloat32 → ComplexFloat

/-- `f z` computed in double precision. -/
public def ComplexFloat32.Native.ref (f : RefFn) (z : ComplexFloat32) : ComplexFloat :=
  refRaw f.code z
