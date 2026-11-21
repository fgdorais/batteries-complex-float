/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat

/-!
# Single-precision complex functions from the C library

`ComplexFloat32.Native.f` calls the C library function for `ComplexFloat32.f`. The results depend
on the platform's C library.
-/

namespace ComplexFloat32.Native

/-- The exponential, computed by the C library function `cexpf`. -/
@[extern "lean_complex_float32_cexp"]
public opaque exp : @& ComplexFloat32 → ComplexFloat32

/-- The principal logarithm, computed by the C library function `clogf`. -/
@[extern "lean_complex_float32_clog"]
public opaque log : @& ComplexFloat32 → ComplexFloat32

/-- The principal square root, computed by the C library function `csqrtf`. -/
@[extern "lean_complex_float32_csqrt"]
public opaque sqrt : @& ComplexFloat32 → ComplexFloat32

/-- The sine, computed by the C library function `csinf`. -/
@[extern "lean_complex_float32_csin"]
public opaque sin : @& ComplexFloat32 → ComplexFloat32

/-- The cosine, computed by the C library function `ccosf`. -/
@[extern "lean_complex_float32_ccos"]
public opaque cos : @& ComplexFloat32 → ComplexFloat32

/-- The tangent, computed by the C library function `ctanf`. -/
@[extern "lean_complex_float32_ctan"]
public opaque tan : @& ComplexFloat32 → ComplexFloat32

/-- The hyperbolic sine, computed by the C library function `csinhf`. -/
@[extern "lean_complex_float32_csinh"]
public opaque sinh : @& ComplexFloat32 → ComplexFloat32

/-- The hyperbolic cosine, computed by the C library function `ccoshf`. -/
@[extern "lean_complex_float32_ccosh"]
public opaque cosh : @& ComplexFloat32 → ComplexFloat32

/-- The hyperbolic tangent, computed by the C library function `ctanhf`. -/
@[extern "lean_complex_float32_ctanh"]
public opaque tanh : @& ComplexFloat32 → ComplexFloat32

/-- The inverse sine, computed by the C library function `casinf`. -/
@[extern "lean_complex_float32_casin"]
public opaque asin : @& ComplexFloat32 → ComplexFloat32

/-- The inverse cosine, computed by the C library function `cacosf`. -/
@[extern "lean_complex_float32_cacos"]
public opaque acos : @& ComplexFloat32 → ComplexFloat32

/-- The inverse tangent, computed by the C library function `catanf`. -/
@[extern "lean_complex_float32_catan"]
public opaque atan : @& ComplexFloat32 → ComplexFloat32

/-- The inverse hyperbolic sine, computed by the C library function `casinhf`. -/
@[extern "lean_complex_float32_casinh"]
public opaque asinh : @& ComplexFloat32 → ComplexFloat32

/-- The inverse hyperbolic cosine, computed by the C library function `cacoshf`. -/
@[extern "lean_complex_float32_cacosh"]
public opaque acosh : @& ComplexFloat32 → ComplexFloat32

/-- The inverse hyperbolic tangent, computed by the C library function `catanhf`. -/
@[extern "lean_complex_float32_catanh"]
public opaque atanh : @& ComplexFloat32 → ComplexFloat32

/-- The projection onto the Riemann sphere, computed by the C library function `cprojf`. -/
@[extern "lean_complex_float32_cproj"]
public opaque proj : @& ComplexFloat32 → ComplexFloat32

/-- The complex conjugate, computed by the C library function `conjf`. -/
@[extern "lean_complex_float32_conj"]
public opaque conj : @& ComplexFloat32 → ComplexFloat32

/-- `z ^ w`, computed by the C library function `cpowf`. -/
@[extern "lean_complex_float32_cpow"]
public opaque pow : @& ComplexFloat32 → @& ComplexFloat32 → ComplexFloat32

/-- Multiplication, as compiled by the C compiler. -/
@[extern "lean_complex_float32_mul"]
public opaque mul : @& ComplexFloat32 → @& ComplexFloat32 → ComplexFloat32

/-- Division, as compiled by the C compiler. -/
@[extern "lean_complex_float32_div"]
public opaque div : @& ComplexFloat32 → @& ComplexFloat32 → ComplexFloat32

/-- The absolute value, computed by the C library function `cabsf`. -/
@[extern "lean_complex_float32_cabs"]
public opaque abs : @& ComplexFloat32 → Float32

/-- The argument, computed by the C library function `cargf`. -/
@[extern "lean_complex_float32_carg"]
public opaque arg : @& ComplexFloat32 → Float32

end ComplexFloat32.Native
