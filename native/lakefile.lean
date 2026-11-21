import Lake
open Lake DSL System

/-!
Bindings for the complex functions of the C library (`<complex.h>`), as an alternative
implementation of `ComplexFloat` functions and as a reference to test the pure Lean ones.
-/

package «batteries-complex-float-native»

require «batteries-complex-float» from ".."

@[default_target]
lean_lib BatteriesComplexFloatNative

/-- Compares the pure Lean functions with the C library. -/
lean_exe compare where
  root := `Compare.ComplexFloat

/-- Measures the accuracy of the pure Lean functions and the C library's against
higher-precision references. -/
lean_exe accuracy where
  root := `Accuracy

/-- Compares the pure Lean `ComplexFloat32` functions with the C library. -/
lean_exe compare32 where
  root := `Compare.ComplexFloat32

target complex_float.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "complex_float.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "complex_float.c"
  -- The C compiler bundled with Lean has no `<complex.h>`, so use the system one.
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

extern_lib libcomplexfloat pkg := do
  let o ← fetch <| pkg.target ``complex_float.o
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "complexfloat") #[o]
