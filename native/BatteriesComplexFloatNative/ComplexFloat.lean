/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat

/-!
# Complex functions from the C library

`ComplexFloat.Native.f` calls the C library function for `ComplexFloat.f`. The results depend on
the platform's C library.
-/

namespace ComplexFloat.Native

/-- The exponential, computed by the C library function `cexp`. -/
@[extern "lean_complex_float_cexp"]
public opaque exp : @& ComplexFloat → ComplexFloat

/-- The principal logarithm, computed by the C library function `clog`. -/
@[extern "lean_complex_float_clog"]
public opaque log : @& ComplexFloat → ComplexFloat

/-- The principal square root, computed by the C library function `csqrt`. -/
@[extern "lean_complex_float_csqrt"]
public opaque sqrt : @& ComplexFloat → ComplexFloat

/-- The sine, computed by the C library function `csin`. -/
@[extern "lean_complex_float_csin"]
public opaque sin : @& ComplexFloat → ComplexFloat

/-- The cosine, computed by the C library function `ccos`. -/
@[extern "lean_complex_float_ccos"]
public opaque cos : @& ComplexFloat → ComplexFloat

/-- The tangent, computed by the C library function `ctan`. -/
@[extern "lean_complex_float_ctan"]
public opaque tan : @& ComplexFloat → ComplexFloat

/-- The hyperbolic sine, computed by the C library function `csinh`. -/
@[extern "lean_complex_float_csinh"]
public opaque sinh : @& ComplexFloat → ComplexFloat

/-- The hyperbolic cosine, computed by the C library function `ccosh`. -/
@[extern "lean_complex_float_ccosh"]
public opaque cosh : @& ComplexFloat → ComplexFloat

/-- The hyperbolic tangent, computed by the C library function `ctanh`. -/
@[extern "lean_complex_float_ctanh"]
public opaque tanh : @& ComplexFloat → ComplexFloat

/-- The inverse sine, computed by the C library function `casin`. -/
@[extern "lean_complex_float_casin"]
public opaque asin : @& ComplexFloat → ComplexFloat

/-- The inverse cosine, computed by the C library function `cacos`. -/
@[extern "lean_complex_float_cacos"]
public opaque acos : @& ComplexFloat → ComplexFloat

/-- The inverse tangent, computed by the C library function `catan`. -/
@[extern "lean_complex_float_catan"]
public opaque atan : @& ComplexFloat → ComplexFloat

/-- The inverse hyperbolic sine, computed by the C library function `casinh`. -/
@[extern "lean_complex_float_casinh"]
public opaque asinh : @& ComplexFloat → ComplexFloat

/-- The inverse hyperbolic cosine, computed by the C library function `cacosh`. -/
@[extern "lean_complex_float_cacosh"]
public opaque acosh : @& ComplexFloat → ComplexFloat

/-- The inverse hyperbolic tangent, computed by the C library function `catanh`. -/
@[extern "lean_complex_float_catanh"]
public opaque atanh : @& ComplexFloat → ComplexFloat

/-- The projection onto the Riemann sphere, computed by the C library function `cproj`. -/
@[extern "lean_complex_float_cproj"]
public opaque proj : @& ComplexFloat → ComplexFloat

/-- The complex conjugate, computed by the C library function `conj`. -/
@[extern "lean_complex_float_conj"]
public opaque conj : @& ComplexFloat → ComplexFloat

/-- `z ^ w`, computed by the C library function `cpow`. -/
@[extern "lean_complex_float_cpow"]
public opaque pow : @& ComplexFloat → @& ComplexFloat → ComplexFloat

/-- Multiplication, as compiled by the C compiler. -/
@[extern "lean_complex_float_mul"]
public opaque mul : @& ComplexFloat → @& ComplexFloat → ComplexFloat

/-- Division, as compiled by the C compiler. -/
@[extern "lean_complex_float_div"]
public opaque div : @& ComplexFloat → @& ComplexFloat → ComplexFloat

/-- The absolute value, computed by the C library function `cabs`. -/
@[extern "lean_complex_float_cabs"]
public opaque abs : @& ComplexFloat → Float

/-- The argument, computed by the C library function `carg`. -/
@[extern "lean_complex_float_carg"]
public opaque arg : @& ComplexFloat → Float

end ComplexFloat.Native
