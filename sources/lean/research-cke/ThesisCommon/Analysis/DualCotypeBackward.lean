import ThesisCommon.Analysis.BanachAdjointNorm
import ThesisCommon.Analysis.EllOneSignedReduction
import ThesisCommon.Analysis.CotypeOperators

/-! UPFP Lemma 4.1: the adjoint cotype estimate for finite ell1 targets.
Coordinate adjoints insert functionals into the genuine Banach dual. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem norm_signed_coordinate_functionals_le {n : ℕ} (R : Fin n → X →L[𝕜] Y)
    (hR : ∀ x, (∑ i, ‖R i x‖) ≤ ‖x‖)
    (f : Fin n → Y →L[𝕜] 𝕜) (hf : ∀ i, ‖f i‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, if θ i then (f i).comp (R i) else -((f i).comp (R i))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [ContinuousLinearMap.sum_apply, one_mul]
  apply le_trans (norm_sum_le _ _) _
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (hR x)
  have h := ((f i).le_opNorm (R i x)).trans
    (mul_le_mul_of_nonneg_right (hf i) (norm_nonneg (R i x)))
  split_ifs <;> simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, norm_neg, one_mul] using h

theorem HasRademacherCotype.dual_ellOne_backward_reduction_power {q C : ℝ}
    (h : HasRademacherCotype (X →L[𝕜] 𝕜) q C) {n : ℕ}
    (T : X →L[𝕜] EllOneSum (Fin n) Y) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (hlarge : C ^ q * M ^ q < (n : ℝ) * (ε/2) ^ q) :
    ∃ i : Fin n, ‖(lpCoordinate 1 i).comp T‖ < ε := by
  obtain ⟨i, hi⟩ := h.exists_small_block_power
    (fun i : Fin n => banachAdjoint (lpCoordinate (𝕜 := 𝕜) (X := Y) 1 i))
    (fun f hf θ => by
      simpa only [banachAdjoint_apply] using norm_signed_coordinate_functionals_le
        (fun i : Fin n => lpCoordinate (𝕜 := 𝕜) (X := Y) 1 i)
        (ellOne_finite_coordinate_sum_le n) f hf θ)
    (banachAdjoint T) hε hM (by simpa only [norm_banachAdjoint] using hT) hlarge
  rw [← banachAdjoint_comp, norm_banachAdjoint] at hi
  exact ⟨i, hi⟩

/-- Lemma 4.1 with the exact threshold printed in the paper. -/
theorem HasRademacherCotype.dual_ellOne_backward_reduction {q C : ℝ}
    (h : HasRademacherCotype (X →L[𝕜] 𝕜) q C) {n : ℕ}
    (T : X →L[𝕜] EllOneSum (Fin n) Y) {ε : ℝ} (hε : 0 < ε)
    (hlarge : 2 * C * ‖T‖ < (n : ℝ) ^ (1/q) * ε) :
    ∃ i : Fin n, ‖(lpCoordinate 1 i).comp T‖ < ε :=
  h.dual_ellOne_backward_reduction_power T hε (norm_nonneg T) le_rfl
    (cotype_power_threshold (by linarith [h.1]) (zero_le_one.trans h.2.1) (norm_nonneg T) hlarge)

theorem HasFiniteCotype.dual_ellOne_backward_width
    (h : HasFiniteCotype (X →L[𝕜] 𝕜)) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∃ N : ℕ, ∀ T : X →L[𝕜] EllOneSum (Fin N) Y, ‖T‖ ≤ M →
      ∃ i : Fin N, ‖(lpCoordinate 1 i).comp T‖ < ε := by
  obtain ⟨q, C, h⟩ := h
  obtain ⟨N, hN⟩ := exists_cotype_power_threshold (q := q) (C := C) (M := M) hε
  exact ⟨N, fun T hT => h.dual_ellOne_backward_reduction_power T hε hM hT hN⟩

end ThesisCommon

