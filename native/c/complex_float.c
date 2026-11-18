#include <lean/lean.h>
#include <complex.h>

/* `ComplexFloat` is a structure with two `Float` fields: a constructor object with no boxed
   fields and 16 bytes of scalar data. */

static inline double complex unbox(b_lean_obj_arg z) {
  return CMPLX(lean_ctor_get_float(z, 0), lean_ctor_get_float(z, sizeof(double)));
}

static inline lean_obj_res box(double complex z) {
  lean_object *r = lean_alloc_ctor(0, 0, 2 * sizeof(double));
  lean_ctor_set_float(r, 0, creal(z));
  lean_ctor_set_float(r, sizeof(double), cimag(z));
  return r;
}

#define UNARY(name) \
  LEAN_EXPORT lean_obj_res lean_complex_float_##name(b_lean_obj_arg z) { \
    return box(name(unbox(z))); \
  }

UNARY(cexp) UNARY(clog) UNARY(csqrt)
UNARY(csin) UNARY(ccos) UNARY(ctan)
UNARY(csinh) UNARY(ccosh) UNARY(ctanh)
UNARY(casin) UNARY(cacos) UNARY(catan)
UNARY(casinh) UNARY(cacosh) UNARY(catanh)
UNARY(cproj) UNARY(conj)

LEAN_EXPORT lean_obj_res lean_complex_float_cpow(b_lean_obj_arg z, b_lean_obj_arg w) {
  return box(cpow(unbox(z), unbox(w)));
}

/* Multiplication and division as compiled by the C compiler (with Annex G semantics unless
   the compiler is told otherwise). */
LEAN_EXPORT lean_obj_res lean_complex_float_mul(b_lean_obj_arg z, b_lean_obj_arg w) {
  return box(unbox(z) * unbox(w));
}

LEAN_EXPORT lean_obj_res lean_complex_float_div(b_lean_obj_arg z, b_lean_obj_arg w) {
  return box(unbox(z) / unbox(w));
}

LEAN_EXPORT double lean_complex_float_cabs(b_lean_obj_arg z) { return cabs(unbox(z)); }
LEAN_EXPORT double lean_complex_float_carg(b_lean_obj_arg z) { return carg(unbox(z)); }
