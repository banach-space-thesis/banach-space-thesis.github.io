import ThesisCommon.Analysis.DualCotypeBackward

/-! A direct adjoint-cotype proof of the forward-selection input to UPFP 3.1.
The manuscript obtains this input through scalar-ell1 compactness. Here the
same finite-sign estimate used in its Lemma 4.1 is applied to disjoint whole
output blocks. This avoids importing an unproved compactness theorem. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem HasRademacherCotype.exists_small_postcomposition_power {q C : ℝ}
    (h : HasRademacherCotype (X →L[𝕜] 𝕜) q C) {n : ℕ}
    (R : Fin n → Y →L[𝕜] Z) (hR : ∀ y, (∑ i, ‖R i y‖) ≤ ‖y‖)
    (T : X →L[𝕜] Y) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (hlarge : C ^ q * M ^ q < (n : ℝ) * (ε/2) ^ q) :
    ∃ i : Fin n, ‖(R i).comp T‖ < ε := by
  obtain ⟨i, hi⟩ := h.exists_small_block_power
    (fun i : Fin n => banachAdjoint (R i))
    (fun f hf θ => by
      simpa only [banachAdjoint_apply] using norm_signed_coordinate_functionals_le R hR f hf θ)
    (banachAdjoint T) hε hM (by simpa only [norm_banachAdjoint] using hT) hlarge
  rw [← banachAdjoint_comp, norm_banachAdjoint] at hi
  exact ⟨i, hi⟩

/-- The exact forward-selection conclusion needed for the ell1 upper reduction. -/
theorem HasFiniteCotype.dual_ellOne_forward_reduction
    (h : HasFiniteCotype (X →L[𝕜] 𝕜)) (T : X →L[𝕜] EllOneSum ℕ Y)
    {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ ↪ ℕ, ‖(lpRestrict 1 m).comp T‖ < ε := by
  obtain ⟨q, C, h⟩ := h
  obtain ⟨N, hN⟩ := exists_cotype_power_threshold (q := q) (C := C) (M := ‖T‖) hε
  obtain ⟨i, hi⟩ := h.exists_small_postcomposition_power
    (fun i : Fin N => lpRestrict (𝕜 := 𝕜) (X := Y) 1 (disjointCoordinateEmbedding i))
    (ellOne_disjoint_restriction_sum_le N) T hε (norm_nonneg T) le_rfl hN
  exact ⟨disjointCoordinateEmbedding i, hi⟩

end ThesisCommon
