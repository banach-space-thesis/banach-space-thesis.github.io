import BanachIsometric.HyperplanePairCoverage
import BanachIsometric.ExactSectionBundleConstruction
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The actual complex Hermitian hyperplane field

The complex Euclidean norm and its existing real restriction are retained.
Polarization proves that the real inner product is the real part of the
complex one even when their PiLp instance dictionaries differ syntactically.
The explicit complex-normal projection is identified with the actual real
canonical orthogonal projection. Its operator Lipschitz constant is `2`.
No Grassmannian regularity premise or substitute norm is introduced.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal Topology ComplexConjugate

noncomputable section

section SharedNorm

variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [InnerProductSpace ℝ V]

/-- Both inner products are determined by the same norm and addition. This
also certifies the usual real PiLp structure on complex Euclidean space. -/
theorem real_inner_eq_complex_re_of_shared_norm (x y : V) :
    inner ℝ x y = (inner ℂ x y).re := by
  calc
    _ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y
    _ = (inner ℂ x y).re :=
      (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) x y).symm

end SharedNorm

section ComplexOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def complexNormalHyperplane (u : V) : Submodule ℂ V :=
  LinearMap.ker ((innerSL ℂ u).toLinearMap : V →ₗ[ℂ] ℂ)

@[simp]
theorem mem_complexNormalHyperplane (u v : V) :
    v ∈ complexNormalHyperplane u ↔ inner ℂ u v = 0 := Iff.rfl

def complexNormalRankOne (u : V) : V →L[ℂ] V := (innerSL ℂ u).smulRight u

def complexNormalProjection (u : V) : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V - complexNormalRankOne u

@[simp]
theorem complexNormalProjection_apply (u v : V) :
    complexNormalProjection u v = v - (inner ℂ u v) • u := rfl

theorem norm_complexNormalRankOne_sub_le (u v : V) :
    ‖complexNormalRankOne u - complexNormalRankOne v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hdec : complexNormalRankOne u - complexNormalRankOne v =
      (innerSL ℂ u).smulRight (u - v) + (innerSL ℂ u - innerSL ℂ v).smulRight v := by
    ext x
    simp only [complexNormalRankOne, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, smul_sub, sub_smul]
    abel
  rw [hdec]
  calc
    ‖(innerSL ℂ u).smulRight (u - v) + (innerSL ℂ u - innerSL ℂ v).smulRight v‖ ≤
        ‖(innerSL ℂ u).smulRight (u - v)‖ + ‖(innerSL ℂ u - innerSL ℂ v).smulRight v‖ := norm_add_le _ _
    _ = (‖u‖ + ‖v‖) * ‖u - v‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply,
        innerSL_apply_norm, ← (innerSL ℂ).map_sub u v, innerSL_apply_norm]
      ring

theorem norm_complexNormalProjection_sub_le (u v : V) :
    ‖complexNormalProjection u - complexNormalProjection v‖ ≤ (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hneg : complexNormalProjection u - complexNormalProjection v =
      -(complexNormalRankOne u - complexNormalRankOne v) := by
    unfold complexNormalProjection
    abel
  rw [hneg, norm_neg]
  exact norm_complexNormalRankOne_sub_le u v

theorem complexNormalHyperplane_finrank_add_one [FiniteDimensional ℂ V]
    (u : V) (hu : ‖u‖ = 1) :
    Module.finrank ℂ (complexNormalHyperplane u) + 1 = Module.finrank ℂ V := by
  let ℓ := (innerSL ℂ u).toLinearMap
  have huu : inner ℂ u u = 1 := by simp [inner_self_eq_norm_sq_to_K, hu]
  have hsurj : Function.Surjective ℓ := by
    intro a
    refine ⟨a • u, ?_⟩
    change inner ℂ u (a • u) = a
    rw [inner_smul_right, huu, mul_one]
  have hdim := ℓ.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hdim
  change 1 + Module.finrank ℂ (complexNormalHyperplane u) = Module.finrank ℂ V at hdim
  omega

end ComplexOperators

section RealRestriction

variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [InnerProductSpace ℝ V] [IsScalarTower ℝ ℂ V]

def realComplexNormalHyperplane (u : V) : Submodule ℝ V :=
  (complexNormalHyperplane u).restrictScalars ℝ

@[simp]
theorem mem_realComplexNormalHyperplane (u v : V) :
    v ∈ realComplexNormalHyperplane u ↔ inner ℂ u v = 0 := Iff.rfl

def realComplexNormalProjection (u : V) : V →L[ℝ] V :=
  (complexNormalProjection u).restrictScalars ℝ

@[simp]
theorem realComplexNormalProjection_apply (u v : V) :
    realComplexNormalProjection u v = v - (inner ℂ u v) • u := rfl

theorem norm_realComplexNormalProjection_sub_le (u v : V) :
    ‖realComplexNormalProjection u - realComplexNormalProjection v‖ ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have heq : realComplexNormalProjection u - realComplexNormalProjection v =
      (complexNormalProjection u - complexNormalProjection v).restrictScalars ℝ := by
    ext x
    rfl
  rw [heq, ContinuousLinearMap.norm_restrictScalars]
  exact norm_complexNormalProjection_sub_le u v

theorem realComplexNormalProjection_lipschitz :
    LipschitzWith 2 (fun u : Metric.sphere (0 : V) 1 ↦ realComplexNormalProjection u.val) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hu : ‖u.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hv : ‖v.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using v.property
  have h := norm_realComplexNormalProjection_sub_le u.val v.val
  simpa only [hu, hv, one_add_one_eq_two, NNReal.coe_ofNat, Subtype.dist_eq, dist_eq_norm] using h

theorem realComplexNormalHyperplane_le_real_perp (u : V) :
    realComplexNormalHyperplane u ≤ (ℝ ∙ u)ᗮ := by
  intro v hv
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [real_inner_eq_complex_re_of_shared_norm, (mem_realComplexNormalHyperplane u v).mp hv]
  rfl

variable [FiniteDimensional ℂ V]

local instance realFiniteDimensional : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V

theorem realComplexNormalProjection_eq_starProjection (u : V) (hu : ‖u‖ = 1) :
    realComplexNormalProjection u = (realComplexNormalHyperplane u).starProjection := by
  have huu : inner ℂ u u = 1 := by simp [inner_self_eq_norm_sq_to_K, hu]
  ext v
  symm
  apply (realComplexNormalHyperplane u).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_realComplexNormalHyperplane, realComplexNormalProjection_apply,
      inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  · intro w hw
    have hd : v - realComplexNormalProjection u v = (inner ℂ u v) • u := by
      rw [realComplexNormalProjection_apply]
      abel
    rw [hd, real_inner_eq_complex_re_of_shared_norm, inner_smul_left,
      (mem_realComplexNormalHyperplane u w).mp hw, mul_zero]
    rfl

theorem realComplexNormalHyperplane_finrank (u : V) (hu : ‖u‖ = 1)
    (n : ℕ) (hdim : Module.finrank ℂ V = n + 1) :
    Module.finrank ℝ (realComplexNormalHyperplane u) = 2 * n := by
  have hcomplex : Module.finrank ℂ (complexNormalHyperplane u) = n := by
    have h := complexNormalHyperplane_finrank_add_one u hu
    omega
  change Module.finrank ℝ ((complexNormalHyperplane u).restrictScalars ℝ) = 2 * n
  have heq : Module.finrank ℂ ((complexNormalHyperplane u).restrictScalars ℝ) = n :=
    ((complexNormalHyperplane u).restrictScalarsEquiv ℝ).finrank_eq.trans hcomplex
  have h := Module.finrank_mul_finrank ℝ ℂ ((complexNormalHyperplane u).restrictScalars ℝ)
  rw [Complex.finrank_real_complex, heq] at h
  exact h.symm

end RealRestriction

abbrev ComplexHermitianAmbient (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))

def complexHyperplaneField (n : ℕ) (u : Metric.sphere (0 : ComplexHermitianAmbient n) 1) :
    Submodule ℝ (ComplexHermitianAmbient n) := realComplexNormalHyperplane u.val

theorem complexHyperplaneField_finrank (n : ℕ)
    (u : Metric.sphere (0 : ComplexHermitianAmbient n) 1) :
    Module.finrank ℝ (complexHyperplaneField n u) = 2 * n := by
  apply realComplexNormalHyperplane_finrank u.val
  · simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  · simp [ComplexHermitianAmbient]

theorem complexHyperplaneField_projection_lipschitz (n : ℕ) :
    LipschitzWith 2 (fun u : Metric.sphere (0 : ComplexHermitianAmbient n) 1 ↦
      (complexHyperplaneField n u).starProjection) := by
  have heq : (fun u : Metric.sphere (0 : ComplexHermitianAmbient n) 1 ↦
      (complexHyperplaneField n u).starProjection) =
      fun u ↦ realComplexNormalProjection u.val := by
    funext u
    exact (realComplexNormalProjection_eq_starProjection u.val
      (by simpa only [Metric.mem_sphere, dist_zero_right] using u.property)).symm
  rw [heq]
  exact realComplexNormalProjection_lipschitz

theorem complexHyperplaneField_le_real_perp (n : ℕ)
    (u : Metric.sphere (0 : ComplexHermitianAmbient n) 1) :
    complexHyperplaneField n u ≤ (ℝ ∙ u.val)ᗮ := realComplexNormalHyperplane_le_real_perp u.val

theorem complexHyperplaneField_pair_coverage (n : ℕ) (hn : 2 ≤ n)
    (x y : ComplexHermitianAmbient n) :
    ∃ u : Metric.sphere (0 : ComplexHermitianAmbient n) 1,
      x ∈ complexHyperplaneField n u ∧ y ∈ complexHyperplaneField n u := by
  obtain ⟨u, hu, hux, huy⟩ := exists_unit_normal_annihilating_pair (𝕜 := ℂ)
    (show 3 ≤ Module.finrank ℂ (ComplexHermitianAmbient n) by
      simp only [ComplexHermitianAmbient, finrank_euclideanSpace_fin]
      omega) x y
  exact ⟨⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩, hux, huy⟩

/-- The complex application supplies the projection regularity and exact
dimension required by the actual real principal exact-section bundle. -/
theorem nonempty_complexHyperplane_exactSectionPrincipalData (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin (2 * n)))) [μ.IsAddHaarMeasure]
    {p : ComplexHermitianAmbient n → ℝ} (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere (0 : ComplexHermitianAmbient n) 1))
    (u₀ : Metric.sphere (0 : ComplexHermitianAmbient n) 1)
    (hequiv : ∀ u, RealSectionEquivalent p (complexHyperplaneField n u₀) (complexHyperplaneField n u)) :
    Nonempty (ExactSectionPrincipalData (2 * n) p (complexHyperplaneField n) u₀) := by
  exact nonempty_exactSectionPrincipalData μ hp hC (complexHyperplaneField n)
    (complexHyperplaneField_projection_lipschitz n)
    (fun u ↦ by simpa only [finrank_euclideanSpace_fin] using complexHyperplaneField_finrank n u)
    u₀ hequiv

end

end BanachIsometric
