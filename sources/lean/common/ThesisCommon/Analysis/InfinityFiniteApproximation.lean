import ThesisCommon.Analysis.LpOperators
import Mathlib.Analysis.RCLike.Lemmas

/-! Finite-range uniform approximation in scalar ℓ∞ over an arbitrary index set. -/

noncomputable section
open scoped ENNReal

namespace ThesisCommon

variable {𝕜 Γ : Type*} [RCLike 𝕜]

/-- Every bounded scalar family admits finite-range uniform approximations that preserve
its zero coordinates and do not increase its norm. No countability or nonemptiness
hypothesis on the index set is needed. -/
theorem infinity_exists_finite_range_approximation
    (x : lp (fun _ : Γ => 𝕜) ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : lp (fun _ : Γ => 𝕜) ∞,
      (Set.range (fun γ => y γ)).Finite ∧
      (∀ γ, x γ = 0 → y γ = 0) ∧ ‖y‖ ≤ ‖x‖ ∧ ‖x - y‖ < ε := by
  classical
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  obtain ⟨s, hs, hfin, hcover⟩ :=
    (isCompact_closedBall (0 : 𝕜) ‖x‖).finite_cover_balls (half_pos hε)
  have hchoose : ∀ γ : Γ, ∃ z ∈ s, ‖x γ - z‖ < ε / 2 := by
    intro γ
    have hx : x γ ∈ Metric.closedBall (0 : 𝕜) ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        lp.norm_apply_le_norm ENNReal.top_ne_zero x γ
    have := hcover hx
    simp only [Set.mem_iUnion, Metric.mem_ball, dist_eq_norm] at this
    obtain ⟨a, ha, hdist⟩ := this
    exact ⟨a, ha, hdist⟩
  choose z hz hdist using hchoose
  let f : Γ → 𝕜 := fun γ => if x γ = 0 then 0 else z γ
  have hf : ∀ γ, ‖f γ‖ ≤ ‖x‖ := by
    intro γ
    dsimp only [f]
    split_ifs
    · simpa only [norm_zero] using norm_nonneg x
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hs (hz γ)
  let y : lp (fun _ : Γ => 𝕜) ∞ := ⟨f, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨γ, rfl⟩
    exact hf γ⟩⟩
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · apply (hfin.insert 0).subset
    rintro _ ⟨γ, rfl⟩
    change f γ ∈ insert 0 s
    dsimp only [f]
    split_ifs
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hz γ)
  · intro γ hγ
    change f γ = 0
    simp only [f, hγ, if_pos]
  · exact lp.norm_le_of_forall_le (norm_nonneg x) hf
  · have hnorm : ‖x - y‖ ≤ ε / 2 := by
      apply lp.norm_le_of_forall_le (half_pos hε).le
      intro γ
      change ‖x γ - f γ‖ ≤ ε / 2
      dsimp only [f]
      split_ifs with hγ
      · simpa only [hγ, sub_self, norm_zero] using (half_pos hε).le
      · exact (hdist γ).le
    exact hnorm.trans_lt (half_lt_self hε)

end ThesisCommon
