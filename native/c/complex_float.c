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

/* `ComplexFloat32` is a structure with two `Float32` fields: 8 bytes of scalar data. */

static inline float complex unbox32(b_lean_obj_arg z) {
  return CMPLXF(lean_ctor_get_float32(z, 0), lean_ctor_get_float32(z, sizeof(float)));
}

static inline lean_obj_res box32(float complex z) {
  lean_object *r = lean_alloc_ctor(0, 0, 2 * sizeof(float));
  lean_ctor_set_float32(r, 0, crealf(z));
  lean_ctor_set_float32(r, sizeof(float), cimagf(z));
  return r;
}

#define UNARY32(name) \
  LEAN_EXPORT lean_obj_res lean_complex_float32_##name(b_lean_obj_arg z) { \
    return box32(name##f(unbox32(z))); \
  }

UNARY32(cexp) UNARY32(clog) UNARY32(csqrt)
UNARY32(csin) UNARY32(ccos) UNARY32(ctan)
UNARY32(csinh) UNARY32(ccosh) UNARY32(ctanh)
UNARY32(casin) UNARY32(cacos) UNARY32(catan)
UNARY32(casinh) UNARY32(cacosh) UNARY32(catanh)
UNARY32(cproj) UNARY32(conj)

LEAN_EXPORT lean_obj_res lean_complex_float32_cpow(b_lean_obj_arg z, b_lean_obj_arg w) {
  return box32(cpowf(unbox32(z), unbox32(w)));
}

LEAN_EXPORT lean_obj_res lean_complex_float32_mul(b_lean_obj_arg z, b_lean_obj_arg w) {
  return box32(unbox32(z) * unbox32(w));
}

LEAN_EXPORT lean_obj_res lean_complex_float32_div(b_lean_obj_arg z, b_lean_obj_arg w) {
  return box32(unbox32(z) / unbox32(w));
}

LEAN_EXPORT float lean_complex_float32_cabs(b_lean_obj_arg z) { return cabsf(unbox32(z)); }
LEAN_EXPORT float lean_complex_float32_carg(b_lean_obj_arg z) { return cargf(unbox32(z)); }
