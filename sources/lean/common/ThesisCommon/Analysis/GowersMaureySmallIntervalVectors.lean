import ThesisCommon.Analysis.GowersMaureyBlockAverages
import ThesisCommon.Analysis.GowersMaureyBlockIncidence

/-! Normalized vectors whose interval norms are arbitrarily close to one
exist in every subspace containing an infinite nonzero block sequence.
The construction uses actual block averages and their incidence bound. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_unit_vector_intervalNorm_le (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Y, implicitNorm D x = 1 ∧ intervalNorm D N x ≤ 1 + ε := by
  classical
  let C := 1 + ε / 2
  have hC : 1 < C := by dsimp [C]; linarith
  have hCpos : 0 < C := zero_lt_one.trans hC
  obtain ⟨m, hm⟩ := exists_nat_gt (max (2 : ℝ) (2 * N * C / ε))
  have hm2R : (2 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm2 : 2 ≤ m := by exact_mod_cast hm2R.le
  have hmpos : (0 : ℝ) < m := by linarith
  have hmerr : 2 * N * C / ε < m := lt_of_le_of_lt (le_max_right _ _) hm
  obtain ⟨x, hxY, hx, hnorm, hsmall⟩ :=
    hasBlockAverage_of_block_sequence D Y u hu hY hne hm2 hC
  refine ⟨∑ i, x i, Y.sum_mem (fun i _ => hxY i), hnorm, ?_⟩
  apply (intervalNorm_successive_sum_bound D N hx
    (div_nonneg hCpos.le hmpos.le) hsmall).trans
  rw [Nat.cast_add]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hmpos).mpr
  have herr : 2 * N * C < (m : ℝ) * ε := (div_lt_iff₀ hε).mp hmerr
  dsimp [C] at herr ⊢
  nlinarith

theorem exists_vector_intervalNorm_le_one (D : ConstructionData 𝕜)
    (Y : Submodule ℝ (C00 𝕜)) (u : ℕ → C00 𝕜)
    (hu : ∀ i j, i < j → Before (u i) (u j))
    (hY : ∀ i, u i ∈ Y) (hne : ∀ i, u i ≠ 0)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Y, implicitNorm D x = (1 + ε)⁻¹ ∧ intervalNorm D N x ≤ 1 := by
  obtain ⟨x, hxY, hxnorm, hxsmall⟩ :=
    exists_unit_vector_intervalNorm_le D Y u hu hY hne N hε
  have hepos : 0 < 1 + ε := by linarith
  have hr : 0 < (1 + ε)⁻¹ := inv_pos.mpr hepos
  refine ⟨(1 + ε)⁻¹ • x, Y.smul_mem _ hxY, ?_, ?_⟩
  · have h := map_smul_eq_mul ((implicitNorm D).restrictScalars ℝ) (1 + ε)⁻¹ x
    change implicitNorm D ((1 + ε)⁻¹ • x) = ‖(1 + ε)⁻¹‖ * implicitNorm D x at h
    simpa only [Real.norm_eq_abs, abs_of_pos hr, hxnorm, mul_one] using h
  · have h := map_smul_eq_mul ((intervalNorm D N).restrictScalars ℝ) (1 + ε)⁻¹ x
    change intervalNorm D N ((1 + ε)⁻¹ • x) = ‖(1 + ε)⁻¹‖ * intervalNorm D N x at h
    rw [h, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hxsmall hr.le).trans_eq (inv_mul_cancel₀ hepos.ne')

end ThesisCommon.GowersMaurey
