# Batteries Complex Float

Complex floating-point numbers for Lean 4: `ComplexFloat`, a pair of `Float`s with the
semantics of C's `double complex` under Annex G of the C standard. This is a Batteries cell: it
builds against [Batteries](https://github.com/leanprover-community/batteries) `main` (and
`nightly-testing` on the `nightly-testing` branch), and can be imported together with it.

```toml
[[require]]
name = "batteries-complex-float"
git = "https://github.com/fgdorais/batteries-complex-float"
rev = "main"
```

## What is in it

- `ComplexFloat` with `re` and `im` fields, literals, `I`, `ofReal`, `ofImag`, `conj`, `+`, `-`,
  `*`, `/`, `inv`, mixed `Float`/`ComplexFloat` arithmetic, `abs`, `normSq`, `arg`, `proj`,
  `polar`, `isNaN`, `isInf`, `isFinite`, and IEEE (componentwise) `==`.
- `exp`, `log`, `sqrt`, `pow` (also as `^` with `ComplexFloat`, `Float` and `Nat` exponents).
- `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh` and their inverses `asin`, `acos`, `atan`,
  `asinh`, `acosh`, `atanh`.
- Scalar helpers on `Float` that core lacks: `signBit`, `copySign`, `exponent?`, `ldexp`,
  `hypot`, `log1p`.

## Semantics

- Multiplication and division follow the reference implementations of Annex G (G.5.1, G.5.2):
  infinities are recovered when the textbook formula gives NaN in both parts, and division
  scales its operands by a power of two to avoid premature overflow and underflow.
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
  Clarendon Press, Oxford, 1987, pp. 165–211.
- C. F. Borges, *Algorithm 1014: An Improved Algorithm for `hypot(x, y)`*, ACM Transactions on
  Mathematical Software 47 (2020), no. 1, Article 9, doi:10.1145/3428446.
- D. Goldberg, *What Every Computer Scientist Should Know About Floating-Point Arithmetic*, ACM
  Computing Surveys 23 (1991), no. 1, 5–48.
- D. E. Knuth, *The Art of Computer Programming, Volume 2: Seminumerical Algorithms*, 3rd ed.,
  Addison-Wesley, 1997, §4.6.3.
- FreeBSD msun (`k_exp.c`, `s_ctanh.c`) and musl libc (`scalbn.c`).

## Proofs

Core arithmetic on `Float` (`+`, `-`, `*`, `/`, `sqrt`, `fma`, bit casts, comparisons) has a
logical model, `Float.Model`, while the transcendental functions are opaque. The arithmetic in
this library, including `ldexp`, `exponent?`, `hypot`, `*` and `/`, is written with modeled
operations only and is exposed, so it can be reasoned about. The other functions are not
exposed.

## Native package and testing

The `native` directory holds a separate package, `batteries-complex-float-native`, with bindings
to the C library's `<complex.h>` (`ComplexFloat.Native.exp` and so on). It needs a system C
compiler with `<complex.h>`, since the compiler bundled with Lean has none. Its `compare`
executable checks the pure Lean functions against the C library on a grid of special inputs
(signed zeros, infinities, NaN, tiny and huge numbers) and on random inputs:

```sh
cd native && lake build compare && .lake/build/bin/compare 50000
```

The test library `BatteriesComplexFloatTest` checks Annex G special values with `#guard` and is
built by CI.

## Branches and workflows

This repository was created from the
[Batteries cell template](https://github.com/leanprover-community/batteries-cell-template); see
there for how the `main` and `nightly-testing` branches and the workflows keep the cell in step
with Batteries.
