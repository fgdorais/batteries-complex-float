/-
Copyright (c) 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesComplexFloat.ComplexFloat32.Basic
public import Batteries.Data.Float.Lemmas.Arithmetic

/-!
# Lemmas about `ComplexFloat32` arithmetic
-/

namespace ComplexFloat32

public theorem _root_.Float32.mulErr_comm (p q : Float32) :
    Float32.mulErr p q = Float32.mulErr q p := by
  simp only [Float32.mulErr]; rw [Float32.fma_comm, Float32.mul_comm]

@[ext] public theorem ext {z w : ComplexFloat32} (hre : z.re = w.re) (him : z.im = w.im) :
    z = w := by
  cases z; cases w; simp_all

@[simp] public theorem re_conj (z : ComplexFloat32) : z.conj.re = z.re := rfl
@[simp] public theorem im_conj (z : ComplexFloat32) : z.conj.im = -z.im := rfl
@[simp] public theorem re_neg (z : ComplexFloat32) : (-z).re = -z.re := rfl
@[simp] public theorem im_neg (z : ComplexFloat32) : (-z).im = -z.im := rfl

@[simp] public theorem conj_conj (z : ComplexFloat32) : z.conj.conj = z := by
  ext <;> simp

@[simp] public theorem neg_neg (z : ComplexFloat32) : - -z = z := by
  ext <;> simp

public theorem conj_neg (z : ComplexFloat32) : (-z).conj = -z.conj := by
  ext <;> simp

public theorem mul_comm (z w : ComplexFloat32) : z * w = w * z := by
  change ComplexFloat32.mul z w = ComplexFloat32.mul w z
  simp only [ComplexFloat32.mul]
  rw [Float32.mul_comm w.re z.re, Float32.mul_comm w.im z.im, Float32.mul_comm w.re z.im,
    Float32.mul_comm w.im z.re, Float32.add_comm (z.im * w.re), Float32.mulErr_comm w.re z.re,
    Float32.mulErr_comm w.im z.im, Float32.mulErr_comm w.re z.im, Float32.mulErr_comm w.im z.re,
    Float32.add_comm (Float32.mulErr z.im w.re),
    Float32.mul_comm w.recoverInf.re, Float32.mul_comm w.recoverInf.im z.recoverInf.im,
    Float32.mul_comm w.recoverInf.re z.recoverInf.im,
    Float32.mul_comm w.recoverInf.im z.recoverInf.re,
    Float32.add_comm (z.recoverInf.im * w.recoverInf.re), Bool.or_comm w.isInf]
  congr 3
  cases (z.re * w.re).isInf <;> cases (z.im * w.im).isInf <;> cases (z.re * w.im).isInf <;>
    cases (z.im * w.re).isInf <;> rfl

end ComplexFloat32
