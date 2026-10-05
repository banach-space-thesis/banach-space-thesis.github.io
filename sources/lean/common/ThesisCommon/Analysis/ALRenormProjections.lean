import ThesisCommon.Analysis.GrothendieckEllOne
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Uniform lower ell-one estimates for finite unconditional projections in
a space isomorphic to ell-one.  This is the analytic estimate used to bound
the disjoint-partition AL renorm; no atomic lattice representation is assumed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
open Grothendieck
attribute [local instance] Classical.decEq
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]

theorem equiv_ellOne_square_sum_le (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (x : J → E) (B : ℝ)
    (hB : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → ‖∑ j, b j • x j‖ ≤ B) :
    (∑ j, ‖x j‖ ^ 2) ≤ (128 * A * C * B) ^ 2 := by
  have hx (j : J) : ‖x j‖ ≤ C * ‖d (x j)‖ := by
    have h := d.symm.toContinuousLinearMap.le_opNorm (d (x j))
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right hdinv (norm_nonneg _))
  have himage : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) → ‖∑ j, b j • d (x j)‖ ≤ A * B := by
    intro b hb
    have heq : (∑ j, b j • d (x j)) = d (∑ j, b j • x j) := by simp
    rw [heq]
    exact (d.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hd (hB b hb) (norm_nonneg _) hA)
  have hs := ellOne_square_sum_le (fun j => d (x j)) (A * B) himage
  calc
    (∑ j, ‖x j‖ ^ 2) ≤ ∑ j, C ^ 2 * ‖d (x j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := (sq_le_sq₀ (norm_nonneg (x j)) (mul_nonneg hC (norm_nonneg _))).mpr (hx j)
      simpa only [mul_pow] using h
    _ = C ^ 2 * ∑ j, ‖d (x j)‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ C ^ 2 * (128 * (A * B)) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg C)
    _ = (128 * A * C * B) ^ 2 := by ring

def projectionTestMap (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (R : J → E →L[ℝ] E)
    (hR : ∀ (x : E) (b : J → ℝ), (∀ j, |b j| ≤ 1) → ‖∑ j, b j • R j x‖ ≤ ‖x‖)
    (φ : J → E →L[ℝ] ℝ) (hφ : ∀ j, ‖φ j‖ ≤ 1) : E →L[ℝ] EuclideanSpace ℝ J :=
  ({ toFun x := WithLp.toLp 2 (fun j => φ j (R j x))
     map_add' x y := by ext j; simp
     map_smul' c x := by ext j; simp } : E →ₗ[ℝ] EuclideanSpace ℝ J).mkContinuous
    (128 * A * C) (fun x => by
      change ‖WithLp.toLp 2 (fun j => φ j (R j x))‖ ≤ 128 * A * C * ‖x‖
      have hs := equiv_ellOne_square_sum_le d A C hA hC hd hdinv (fun j => R j x) ‖x‖ (hR x)
      have hφval (j : J) : |φ j (R j x)| ≤ ‖R j x‖ := by
        exact (φ j).le_opNorm (R j x) |>.trans
          ((mul_le_mul_of_nonneg_right (hφ j) (norm_nonneg _)).trans_eq (one_mul _))
      have hsq : ‖WithLp.toLp 2 (fun j => φ j (R j x))‖ ^ 2 ≤ ∑ j, ‖R j x‖ ^ 2 := by
        rw [euclidean_norm_sq]
        apply Finset.sum_le_sum
        intro j _
        have h := (sq_le_sq₀ (abs_nonneg (φ j (R j x))) (norm_nonneg (R j x))).mpr (hφval j)
        simpa only [sq_abs] using h
      have hnon : 0 ≤ 128 * A * C * ‖x‖ := by positivity
      nlinarith [norm_nonneg (WithLp.toLp 2 (fun j => φ j (R j x)))])

theorem projectionTestMap_apply (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (R : J → E →L[ℝ] E)
    (hR : ∀ (x : E) (b : J → ℝ), (∀ j, |b j| ≤ 1) → ‖∑ j, b j • R j x‖ ≤ ‖x‖)
    (φ : J → E →L[ℝ] ℝ) (hφ : ∀ j, ‖φ j‖ ≤ 1) (x : E) (j : J) :
    projectionTestMap d A C hA hC hd hdinv R hR φ hφ x j = φ j (R j x) := rfl

theorem projectionTestMap_norm_le (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (R : J → E →L[ℝ] E)
    (hR : ∀ (x : E) (b : J → ℝ), (∀ j, |b j| ≤ 1) → ‖∑ j, b j • R j x‖ ≤ ‖x‖)
    (φ : J → E →L[ℝ] ℝ) (hφ : ∀ j, ‖φ j‖ ≤ 1) :
    ‖projectionTestMap d A C hA hC hd hdinv R hR φ hφ‖ ≤ 128 * A * C :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Uniformity in both the number of projections and their ranges is the
essential lower estimate. It applies in particular to finite disjoint band
projections; their scalar cube bound is precisely solidity of the lattice norm. -/
theorem unconditional_projection_sum_norm_le
    (d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1) (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hd : ‖d.toContinuousLinearMap‖ ≤ A) (hdinv : ‖d.symm.toContinuousLinearMap‖ ≤ C)
    (R : J → E →L[ℝ] E)
    (hR : ∀ (x : E) (b : J → ℝ), (∀ j, |b j| ≤ 1) → ‖∑ j, b j • R j x‖ ≤ ‖x‖)
    (horth : ∀ (i j : J) (x : E), R i (R j x) = if i = j then R j x else 0)
    (x : E) : (∑ j, ‖R j x‖) ≤ (128 * A * C) ^ 2 * ‖x‖ := by
  classical
  choose φ hφ hφx using fun j => exists_dual_vector'' ℝ (R j x)
  let S := projectionTestMap d A C hA.le hC.le hd hdinv R hR φ hφ
  have hS : ‖S‖ ≤ 128 * A * C := projectionTestMap_norm_le d A C hA.le hC.le hd hdinv R hR φ hφ
  have hnorm (j : J) : ‖S (R j x)‖ = ‖R j x‖ := by
    have heq : S (R j x) = EuclideanSpace.single j ‖R j x‖ := by
      ext i
      change φ i (R i (R j x)) = (EuclideanSpace.single j ‖R j x‖) i
      rw [horth]
      by_cases hij : i = j
      · subst i
        simp [hφx]
      · simp [hij, Ne.symm hij]
    rw [heq, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hnormT : ‖S.comp d.symm.toContinuousLinearMap‖ ≤ 128 * A * C * C :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hS hdinv (norm_nonneg _) (by positivity))
  have hcube : ∀ b : J → ℝ, (∀ j, |b j| ≤ 1) →
      ‖∑ j, b j • d (R j x)‖ ≤ A * ‖x‖ := by
    intro b hb
    have heq : (∑ j, b j • d (R j x)) = d (∑ j, b j • R j x) := by simp
    rw [heq]
    exact (d.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hd (hR x b hb) (norm_nonneg _) hA.le)
  have h := ellOne_hilbert_sum_norm_le (S.comp d.symm.toContinuousLinearMap)
    (fun j => d (R j x)) (A * ‖x‖) (128 * A * C * C) (by positivity) hnormT hcube
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, hnorm] at h
  convert h using 1 <;> ring

end ThesisCommon
