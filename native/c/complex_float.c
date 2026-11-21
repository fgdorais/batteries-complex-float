#include <lean/lean.h>
#include <complex.h>
#include <math.h>

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

/* Reference values for accuracy measurements. `ComplexFloat` functions are compared with the
   `long double complex` functions (64-bit significand on x86-64), returned as a rounded value
   `hi` and the remainder `lo`, so that `hi + lo` keeps the extra precision. `ComplexFloat32`
   functions are compared with the `double complex` functions on the same inputs. */

static long double complex ref_ld(uint32_t op, long double complex z) {
  switch (op) {
    case 0: return cexpl(z);   case 1: return clogl(z);   case 2: return csqrtl(z);
    case 3: return csinl(z);   case 4: return ccosl(z);   case 5: return ctanl(z);
    case 6: return csinhl(z);  case 7: return ccoshl(z);  case 8: return ctanhl(z);
    case 9: return casinl(z);  case 10: return cacosl(z); case 11: return catanl(z);
    case 12: return casinhl(z); case 13: return cacoshl(z); case 14: return catanhl(z);
    case 15: return cabsl(z);  case 16: return cargl(z);
    default: return NAN;
  }
}

static double complex ref_d(uint32_t op, double complex z) {
  switch (op) {
    case 0: return cexp(z);   case 1: return clog(z);   case 2: return csqrt(z);
    case 3: return csin(z);   case 4: return ccos(z);   case 5: return ctan(z);
    case 6: return csinh(z);  case 7: return ccosh(z);  case 8: return ctanh(z);
    case 9: return casin(z);  case 10: return cacos(z); case 11: return catan(z);
    case 12: return casinh(z); case 13: return cacosh(z); case 14: return catanh(z);
    case 15: return cabs(z);  case 16: return carg(z);
    default: return NAN;
  }
}

/* A `ComplexFloat.Native.Ref`: four `Float` fields `hiRe`, `hiIm`, `loRe`, `loIm`. */
LEAN_EXPORT lean_obj_res lean_complex_float_ref(uint32_t op, b_lean_obj_arg z) {
  long double complex w = ref_ld(op, CMPLXL(lean_ctor_get_float(z, 0),
                                           lean_ctor_get_float(z, sizeof(double))));
  double hr = (double)creall(w), hi = (double)cimagl(w);
  lean_object *r = lean_alloc_ctor(0, 0, 4 * sizeof(double));
  lean_ctor_set_float(r, 0, hr);
  lean_ctor_set_float(r, sizeof(double), hi);
  lean_ctor_set_float(r, 2 * sizeof(double), (double)(creall(w) - hr));
  lean_ctor_set_float(r, 3 * sizeof(double), (double)(cimagl(w) - hi));
  return r;
}

LEAN_EXPORT lean_obj_res lean_complex_float32_ref(uint32_t op, b_lean_obj_arg z) {
  return box(ref_d(op, CMPLX((double)lean_ctor_get_float32(z, 0),
                             (double)lean_ctor_get_float32(z, sizeof(float)))));
}
