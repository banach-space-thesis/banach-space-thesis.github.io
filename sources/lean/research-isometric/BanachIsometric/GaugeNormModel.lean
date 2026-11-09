import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-! A genuine norm model for a positive real bilinear gauge. The original
space may carry an unrelated compatible metric; its topology and metric are
not overwritten. All normed structures live on the explicit type tag. -/

namespace BanachIsometric.MetricGeometry

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

structure PositiveGaugeData (q : X → ℝ) where
  bilinear : X →ₗ[ℝ] X →ₗ[ℝ] ℝ
  symmetric : ∀ x y, bilinear x y = bilinear y x
  diagonal : ∀ x, bilinear x x = q x ^ 2
  nonneg : ∀ x, 0 ≤ q x
  eq_zero_iff : ∀ x, q x = 0 ↔ x = 0

def PositiveGaugeData.core {q : X → ℝ} (D : PositiveGaugeData q) : InnerProductSpace.Core ℝ X where
  inner x y := D.bilinear x y
  conj_inner_symm x y := D.symmetric y x
  re_inner_nonneg x := by change 0 ≤ D.bilinear x x; rw [D.diagonal]; exact sq_nonneg _
  definite x hx := D.eq_zero_iff x |>.mp (sq_eq_zero_iff.mp (by rwa [D.diagonal] at hx))
  add_left x y z := by rw [D.bilinear.map_add]; rfl
  smul_left x y r := by change D.bilinear (r • x) y = r * D.bilinear x y; rw [D.bilinear.map_smul]; rfl

def GaugeNormModel {q : X → ℝ} (_D : PositiveGaugeData q) : Type _ := X

instance {q : X → ℝ} (D : PositiveGaugeData q) : AddCommGroup (GaugeNormModel D) :=
  inferInstanceAs (AddCommGroup X)

instance {q : X → ℝ} (D : PositiveGaugeData q) : Module ℝ (GaugeNormModel D) :=
  inferInstanceAs (Module ℝ X)

instance {q : X → ℝ} (D : PositiveGaugeData q) : NormedAddCommGroup (GaugeNormModel D) :=
  D.core.toNormedAddCommGroup

instance {q : X → ℝ} (D : PositiveGaugeData q) : InnerProductSpace ℝ (GaugeNormModel D) :=
  InnerProductSpace.ofCore D.core

theorem norm_gaugeNormModel {q : X → ℝ} (D : PositiveGaugeData q) (x : GaugeNormModel D) :
    ‖x‖ = q (x : X) := by
  have h := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) x
  change ‖x‖ ^ 2 = D.bilinear (x : X) x at h
  rw [D.diagonal] at h
  exact (sq_eq_sq₀ (norm_nonneg x) (D.nonneg x)).mp h

def toGaugeNormModel {q : X → ℝ} (D : PositiveGaugeData q) : X ≃ₗ[ℝ] GaugeNormModel D :=
  LinearEquiv.refl ℝ X

section ExtraScalars

variable {R : Type*} [Semiring R] [Module R X]

instance {q : X → ℝ} (D : PositiveGaugeData q) : Module R (GaugeNormModel D) :=
  inferInstanceAs (Module R X)

instance {q : X → ℝ} (D : PositiveGaugeData q) [SMul ℝ R] [IsScalarTower ℝ R X] :
    IsScalarTower ℝ R (GaugeNormModel D) := inferInstanceAs (IsScalarTower ℝ R X)

def toGaugeNormModelScalar {q : X → ℝ} (D : PositiveGaugeData q) : X ≃ₗ[R] GaugeNormModel D :=
  LinearEquiv.refl R X

variable [Norm R]

def gaugeNormModelNormSMul {q : X → ℝ} (D : PositiveGaugeData q)
    (hscale : ∀ (a : R) (x : X), q (a • x) = ‖a‖ * q x) : NormSMulClass R (GaugeNormModel D) where
  norm_smul a x := by rw [norm_gaugeNormModel, norm_gaugeNormModel]; exact hscale a x

end ExtraScalars

end
end BanachIsometric.MetricGeometry
