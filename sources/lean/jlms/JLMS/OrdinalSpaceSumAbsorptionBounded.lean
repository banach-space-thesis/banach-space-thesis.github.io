import JLMS.OrdinalSpaceSumAbsorption

/-!
# Uniform bounds for absorption into a constant c₀ sum

Splitting off one coordinate and reassociating are isometries, so the
absorption construction preserves any common bound at least one.
-/

noncomputable section
namespace JLMS
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_cZeroSumAbsorbs_le (I : Type u) [Infinite I]
    (e : (F × E) ≃L[𝕜] E) {C : ℝ} (hC : 1 ≤ C)
    (he : ∀ x, ‖e x‖ ≤ C * ‖x‖)
    (x : F × CZeroSum 𝕜 (fun _ : I => E)) :
    ‖cZeroSumAbsorbs I e x‖ ≤ C * ‖x‖ := by
  let h := cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) I E
  change ‖h.symm (e (x.1, (h x.2).1), (h x.2).2)‖ ≤ _
  rw [h.symm.norm_map, Prod.norm_def]
  have hx : ‖h x.2‖ ≤ ‖x‖ := (h.norm_map x.2).le.trans (le_max_right _ _)
  have hx₁ : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _
  have hh₁ : ‖(h x.2).1‖ ≤ ‖h x.2‖ := le_max_left _ _
  have hh₂ : ‖(h x.2).2‖ ≤ ‖h x.2‖ := le_max_right _ _
  apply max_le
  · exact (he _).trans (mul_le_mul_of_nonneg_left
      (max_le hx₁ (hh₁.trans hx)) (zero_le_one.trans hC))
  · exact (hh₂.trans hx).trans (le_mul_of_one_le_left (norm_nonneg _) hC)

theorem norm_cZeroSumAbsorbs_symm_le (I : Type u) [Infinite I]
    (e : (F × E) ≃L[𝕜] E) {C : ℝ} (hC : 1 ≤ C)
    (he : ∀ x, ‖e.symm x‖ ≤ C * ‖x‖)
    (x : CZeroSum 𝕜 (fun _ : I => E)) :
    ‖(cZeroSumAbsorbs I e).symm x‖ ≤ C * ‖x‖ := by
  let h := cZeroSumInfiniteHeadIsometry (𝕜 := 𝕜) I E
  change max ‖(e.symm (h x).1).1‖
    ‖h.symm ((e.symm (h x).1).2, (h x).2)‖ ≤ _
  rw [h.symm.norm_map, Prod.norm_def]
  have hx : ‖h x‖ = ‖x‖ := h.norm_map x
  have hh₁ : ‖(h x).1‖ ≤ ‖x‖ := (le_max_left _ _).trans hx.le
  have hh₂ : ‖(h x).2‖ ≤ ‖x‖ := (le_max_right _ _).trans hx.le
  have hb := (he ((h x).1)).trans
    (mul_le_mul_of_nonneg_left hh₁ (zero_le_one.trans hC))
  have hb₁ : ‖(e.symm (h x).1).1‖ ≤ ‖e.symm (h x).1‖ := le_max_left _ _
  have hb₂ : ‖(e.symm (h x).1).2‖ ≤ ‖e.symm (h x).1‖ := le_max_right _ _
  exact max_le (hb₁.trans hb) (max_le (hb₂.trans hb)
    (hh₂.trans (le_mul_of_one_le_left (norm_nonneg _) hC)))

end JLMS
