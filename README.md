# Batteries Complex Float

Complex floating-point numbers for Lean 4, in two precisions: `ComplexFloat`, a pair of
`Float`s with the semantics of C's `double complex` under Annex G of the C standard, and
`ComplexFloat32`, a pair of `Float32`s with the semantics of C's `float complex`. This is a
Batteries cell: it builds against
[Batteries](https://github.com/leanprover-community/batteries) `main` (and `nightly-testing` on
the `nightly-testing` branch), and can be imported together with it. For now, `main` requires
the Batteries branch `float-utils`, whose `Float.signBit`, `Float.copySign` and `fma_comm` it
uses; it goes back to Batteries `main` once that branch is merged.

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
  four products, and each part of a product is within 1 ulp of the exact value in tests.
  Division computes its numerators with Kahan's algorithm, and also scales both operands by
  powers of two so that nothing overflows or underflows early. Each part of a quotient is within
  3 ulps of the exact value in tests.
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

The test library `BatteriesComplexFloatTest` is built by CI. It checks Annex G special values
with `#guard`, in both precisions, and checks multiplication and division against exact
rational arithmetic: each part of a product within 1 ulp and of a quotient within 3 ulps of the
exact result, on random inputs over the whole exponent range and on inputs with cancellation.

## Branches and workflows

This repository was created from the
[Batteries cell template](https://github.com/leanprover-community/batteries-cell-template); see
there for how the `main` and `nightly-testing` branches and the workflows keep the cell in step
with Batteries.
