import ThesisCommon.Analysis.JamesFiniteBlocks
import ThesisCommon.Analysis.JamesMonotonePathEndpoints
import ThesisCommon.Analysis.JamesDisjointEstimate

/-! The norm of a finite block can be witnessed by paths inside its closed
boundary interval. Zero boundary values make clamping preserve every edge. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)

theorem jamesIntervalBlock_clamp {lo hi : ℕ} (hlh : lo ≤ hi)
    (x : JamesIntervalBlock 𝕜 p lo hi) (n : ℕ) :
    x.val (max lo (min hi n)) = x.val n := by
  by_cases hl : n ≤ lo
  · rw [min_eq_right (hl.trans hlh), max_eq_left hl,
      x.property lo (Or.inl le_rfl), x.property n (Or.inl hl)]
  · by_cases hh : hi ≤ n
    · rw [min_eq_left hh, max_eq_right hlh,
        x.property hi (Or.inr le_rfl), x.property n (Or.inr hh)]
    · rw [min_eq_right (le_of_not_ge hh), max_eq_right (le_of_not_ge hl)]

include hp in
theorem jamesIntervalBlock_path_inside {lo hi : ℕ} (hlh : lo ≤ hi)
    (x : JamesIntervalBlock 𝕜 p lo hi) (s : JamesPath) :
    ∃ t : JamesPath, lo ≤ t.index 0 ∧ t.index (Fin.last t.length) ≤ hi ∧
      ‖jamesPathMap 𝕜 p s x.val.val‖ ^ p.val.toReal =
        ‖jamesPathMap 𝕜 p t x.val.val‖ ^ p.val.toReal := by
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  let f : Fin (s.length + 1) → ℕ := fun j => max lo (min hi (s.index j))
  have hf : Monotone f := by
    intro i j hij
    exact max_le_max le_rfl (min_le_min le_rfl (s.strictMono.monotone hij))
  let w : ℕ → ℕ → ℝ := fun i j => ‖x.val i - x.val j‖ ^ p.val.toReal
  obtain ⟨t, ht0, htl, ht⟩ := exists_jamesPath_of_monotone_endpoints w
    (fun i => by simp only [w, sub_self, norm_zero, Real.zero_rpow hq.ne']) f hf
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [ht0]
    exact le_max_left _ _
  · rw [htl]
    exact max_le hlh (min_le_left _ _)
  · rw [finitePiLp_norm_rpow p hp, finitePiLp_norm_rpow p hp]
    change (∑ j : Fin s.length, w (s.index j.castSucc) (s.index j.succ)) =
      ∑ j : Fin t.length, w (t.index j.castSucc) (t.index j.succ)
    rw [← ht]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [w, f]
    rw [jamesIntervalBlock_clamp p hlh, jamesIntervalBlock_clamp p hlh]

include hp in
theorem jamesIntervalBlock_exists_path_gt {lo hi : ℕ} (hlh : lo ≤ hi)
    (x : JamesIntervalBlock 𝕜 p lo hi) {C : ℝ} (hC : C < ‖x‖ ^ p.val.toReal) :
    ∃ s : JamesPath, lo ≤ s.index 0 ∧ s.index (Fin.last s.length) ≤ hi ∧
      C < ‖jamesPathMap 𝕜 p s x.val.val‖ ^ p.val.toReal := by
  have hex : ∃ s : JamesPath, C < ‖jamesPathMap 𝕜 p s x.val.val‖ ^ p.val.toReal := by
    by_contra hn
    push_neg at hn
    have hC0 : 0 ≤ C := (Real.rpow_nonneg (norm_nonneg _) _).trans (hn (JamesPath.point 0))
    have hbound := james_norm_rpow_le_of_path p hp (x := x.val) hC0 hn
    exact (not_lt_of_ge hbound) hC
  obtain ⟨s, hs⟩ := hex
  obtain ⟨t, ht0, htl, ht⟩ := jamesIntervalBlock_path_inside p hp hlh x s
  exact ⟨t, ht0, htl, hs.trans_eq ht⟩

end ThesisCommon
