# Batteries Complex Float

Complex floating-point numbers for Lean 4, in two precisions: `ComplexFloat`, a pair of
`Float`s with the semantics of C's `double complex` under Annex G of the C standard, and
`ComplexFloat32`, a pair of `Float32`s with the semantics of C's `float complex`. This is a
Batteries cell: it builds against
[Batteries](https://github.com/leanprover-community/batteries) `main` (and `nightly-testing` on
the `nightly-testing` branch), and can be imported together with it.

```toml
[[require]]
name = "batteries-complex-float"
git = "https://github.com/fgdorais/batteries-complex-float"
rev = "main"
```

## What is in it

Both types have the same API, with the same algorithms and each precision's own thresholds and
constants:

- `re` and `im` fields, literals, `I`, `ofReal`, `ofImag`, `conj`, `+`, `-`, `*`, `/`, `inv`,
  mixed real and complex arithmetic, `abs`, `normSq`, `arg`, `proj`, `polar`, `isNaN`, `isInf`,
  `isFinite`, and IEEE (componentwise) `==`.
- `exp`, `log`, `sqrt`, `pow` (also as `^` with complex, real and `Nat` exponents).
- `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh` and their inverses `asin`, `acos`, `atan`,
  `asinh`, `acosh`, `atanh`.
- Scalar helpers on `Float` and `Float32` that core lacks: `exponent?`, `ldexp`, `mulErr` (the
  exact rounding error of a product, by `fma`), `hypot`, `log1p`.

## Layout

`BatteriesComplexFloat.ComplexFloat` and `BatteriesComplexFloat.ComplexFloat32` import
everything for one type, and the root `BatteriesComplexFloat` imports both. Each has the same
modules: `Scalar` (helpers on the real type), `Basic` (the type and its arithmetic), `Exp`,
`Trig`, `Inverse`, `Lemmas.Basic` and `Lemmas.SpecialValues`.
The tests in `BatteriesComplexFloatTest`, the C bindings in `native/BatteriesComplexFloatNative`
and the comparison tools in `native/Compare` are split the same way.

## Semantics

- Multiplication and division follow the reference implementations of Annex G (G.5.1, G.5.2):
  infinities are recovered when the textbook formula gives NaN in both parts. Both use fused
  multiply-adds to stay accurate under cancellation, where the textbook formula and the C
  library can lose every digit of a part. Multiplication adds back the rounding errors of its
  four products, so each part of a product is within 1 ulp of the exact value in our
  measurements. Division computes its numerators with Kahan's algorithm, and also scales both
  operands by powers of two so that nothing overflows or underflows early. Each part of a
  quotient is within 4 ulps of the exact value. See [Accuracy](#accuracy).
- Mixed real and complex operations treat the real operand as having no imaginary part, so signs
  of zeros survive. There is deliberately no coercion from `Float` to `ComplexFloat`; give
  literals type `Float` in complex expressions, as in `(1 : Float) - z`.
- The elementary functions have the special values of Annex G (G.6) and put their branch cuts
  where Annex G does, with the sign of a zero imaginary (or real) part choosing the side of the
  cut. The inverse functions use the formulas from W. Kahan, *Branch Cuts for Complex
  Elementary Functions, or Much Ado About Nothing's Sign Bit* (1987).
- `abs` uses a scaled `hypot` with the correction step of Borges (2019), and `exp`, `sinh` and
  `cosh` avoid premature overflow for large real parts as FreeBSD's libm does.
- Lean's `Float` has a canonical NaN without sign or payload, so where Annex G leaves the sign of
  a result unspecified the choice can differ from a C library that propagates NaN signs.

## Accuracy

The table gives the largest error measured in each part of the result, in ulps of that part,
for the pure Lean functions and for glibc's `<complex.h>` on the same inputs. The inputs are
200,000 random numbers in each of four sets: parts with exponents in `[-4, 4)`, in `[-60, 60)`
(`[-30, 30)` for `Float32`), over the whole exponent range, and numbers near the unit circle
and the branch points `±1` and `±I`. Products and quotients are compared with the exact result
in `Rat`, and the elementary functions with glibc's `long double complex` functions (11 more
bits) for `ComplexFloat` and its `double complex` functions for `ComplexFloat32`. Inputs whose
reference is not finite are skipped. The `accuracy` executable in `native/` regenerates the
full tables, by input set and with normwise errors too:

```sh
cd native && lake build accuracy && .lake/build/bin/accuracy 200000
```

| function | `ComplexFloat` | glibc `double` | `ComplexFloat32` | glibc `float` |
|---|---|---|---|---|
| `*` | **1.00** | 32,044 | **1.11** | 36,081 |
| `/` | **3.76** | ∞ | **3.20** (13.9 ¹) | ∞ |
| `abs` | 1.00 | 1.00 | 0.75 | 0.50 |
| `arg` | 0.52 | 0.52 | 1.45 | 1.45 |
| `exp` | 1.93 | 1.93 | 1.90 | 1.90 |
| `log` | 2.73 | 2.46 | 2.54 | 2.46 |
| `sqrt` | 2.19 | 2.19 | 2.04 | 2.04 |
| `sin`, `cos` | 2.85 | 2.85 | 2.81 | 2.81 |
| `tan` | 5.61 | 5.77 | **5.35** | 7.16 |
| `sinh`, `cosh` | 2.86 | 2.86 | 2.99 | 2.99 |
| `tanh` | 5.73 | 5.81 | 5.09 | 5.84 |
| `asin` | 4.30 | 4.25 | 4.29 | 3.80 |
| `acos`, `acosh` | 3.85 | 4.25 | 3.85 | 3.82 |
| `atan` | **4.08** | 4.84 | **3.75** | 5.30 |
| `asinh` | 4.13 | 4.61 | 4.24 | 4.11 |
| `atanh` | **4.01** | 4.87 | **3.86** | 5.01 |

¹ When the parts of an operand differ by more than a factor of about `2 ^ 187`, the smaller one
is subnormal once the operand is scaled. The error relative to the norm of the quotient is
still below 4 ulps.

Where we do better than glibc:

- **Multiplication and division.** glibc uses the textbook formula, which loses every digit of
  a part when its two products nearly cancel: 32,044 ulps in a part of a product with
  exponents in `[-4, 4)`, and 501,626 ulps in a part of a quotient. glibc's division also
  overflows or underflows early, so over the whole exponent range it returns infinite or zero
  parts for finite, nonzero quotients (the ∞ in the table). Ours stays within 1 ulp for
  products (1.11 ulps for subnormal `Float32` results) and 4 ulps for quotients (except as in
  the note). Measured normwise, both are within 4 ulps where glibc does not overflow.
- **`atan`, `atanh`, `tan` and `tanh`.** Up to 1.8 ulps better on the worst case, and more
  inputs where glibc is off by over 1 ulp more than ours than the reverse.

`exp`, `sqrt`, `sin`, `cos`, `sinh` and `cosh` are as accurate as glibc's: both are built the
same way from the same real functions. glibc is slightly better on the worst case of `log` and
`asin` and, for `Float32`, of `asinh` and `abs`.

The CI tests check smaller samples: products within 1 ulp and quotients within 3 ulps of the
exact result in both precisions, and each `ComplexFloat32` function against `ComplexFloat`, to
the bounds of the table rounded up to the next half ulp (6 ulps for `tan` and `tanh`).

## References

Each module lists its references, and each docstring cites the ones its algorithm follows:

- ISO/IEC 9899:2018 (C17) and ISO/IEC 9899:2024 (C23), Annex G, *IEC 60559-compatible complex
  arithmetic*.
- IEEE Std 754-2019, *IEEE Standard for Floating-Point Arithmetic*.
- W. Kahan, *Branch Cuts for Complex Elementary Functions, or Much Ado About Nothing's Sign Bit*,
  in A. Iserles and M. J. D. Powell (eds.), *The State of the Art in Numerical Analysis*,
  Clarendon Press, Oxford, 1987.
- C. F. Borges, *Algorithm 1014: An Improved Algorithm for `hypot(x, y)`*, ACM Transactions on
  Mathematical Software 47 (2020), no. 1, Article 9, doi:10.1145/3428446.
- C.-P. Jeannerod, N. Louvet and J.-M. Muller, *Further analysis of Kahan's algorithm for the
  accurate computation of 2 × 2 determinants*, Mathematics of Computation 82 (2013), no. 284,
  2245–2264.
- C.-P. Jeannerod, N. Louvet and J.-M. Muller, *On the componentwise accuracy of complex
  floating-point division with an FMA*, in 21st IEEE Symposium on Computer Arithmetic
  (ARITH 2013), IEEE, 2013.
- D. Goldberg, *What Every Computer Scientist Should Know About Floating-Point Arithmetic*, ACM
  Computing Surveys 23 (1991), no. 1, 5–48.
- D. E. Knuth, *The Art of Computer Programming, Volume 2: Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, §4.6.3.
- FreeBSD msun (`k_exp.c`, `k_expf.c`, `s_ctanh.c`, `s_ctanhf.c`) and musl libc (`scalbn.c`,
  `scalbnf.c`).

## Proofs

Core arithmetic on `Float` and `Float32` (`+`, `-`, `*`, `/`, `sqrt`, `fma`, bit casts, comparisons)
has logical models, `Float.Model` and `Float32.Model`, while the transcendental functions are
opaque. The arithmetic in this library, including `ldexp`, `exponent?`, `hypot`, `*` and `/`, is
written with modeled operations only and is exposed, so it can be reasoned about. The other
functions are not exposed.

- The cell imports three Batteries modules: `Batteries.Data.Float.Basic` (for `Float.pi`),
  `Batteries.Data.Float.Bits` (for `signBit` and `copySign`) and
  `Batteries.Data.Float.Lemmas.Arithmetic`, which proves `neg_neg`, `neg_mul`, `mul_neg`,
  `neg_div`, `div_neg`, `mul_comm`, `add_comm` and `fma_comm` through the model.
- `Lemmas.Basic` proves `ext`, `conj_conj`, `neg_neg`, `conj_neg` and `mul_comm`, for each
  type.
- `Lemmas.SpecialValues` proves Annex G special values of `*`, `/`, `abs` and `proj` by
  evaluating the model in the kernel (`decide +kernel`), and that `conj (z * w) = conj z *
  conj w` fails on a sign of zero, for each type.

Identities such as `-(x + y) = -x + -y` are false in IEEE arithmetic (`x + (-x)` is `+0`), so
the lemmas that hold are the sign-symmetric ones for `*` and `/` and the commutativity of `+`
and `*`.

## Native package and testing

The `native` directory holds a separate package, `batteries-complex-float-native`, with bindings
to the C library's `<complex.h>` (`ComplexFloat.Native.exp`, `ComplexFloat32.Native.exp` and
so on). It needs a system C
compiler with `<complex.h>`, since the compiler bundled with Lean has none. Its `compare`
executable checks the pure Lean functions against the C library on a grid of special inputs
(signed zeros, infinities, NaN, tiny and huge numbers) and on random inputs. It reports many
multiplication and division mismatches on extreme inputs. These come from the C library's less
accurate formulas, and from the sign of a part of a quotient that underflows to zero:

```sh
cd native && lake build compare && .lake/build/bin/compare 50000
```

The `compare32` executable does the same for `ComplexFloat32` against the `float complex`
functions.

The `accuracy` executable measures accuracy against higher-precision references (see
[Accuracy](#accuracy)).

The test library `BatteriesComplexFloatTest` is built by CI. It checks Annex G special values
with `#guard`, in both precisions. It checks multiplication and division against exact rational
arithmetic: each part of a product within 1 ulp and of a quotient within 3 ulps of the exact
result, on random inputs over the whole exponent range and on inputs with cancellation. It also
checks each `ComplexFloat32` function against the `ComplexFloat` one.

## Branches and workflows

This repository was created from the
[Batteries cell template](https://github.com/leanprover-community/batteries-cell-template); see
there for how the `main` and `nightly-testing` branches and the workflows keep the cell in step
with Batteries.
