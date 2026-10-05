import ThesisCommon.Analysis.BanachMazurDistance

/-! The closed infimum bound has actual isomorphisms with every strictly
larger distortion bound. This keeps endpoint attainment separate, as required
by the source discrepancy in Definition 2.1. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
universe u v
variable (𝕜 : Type*) [RCLike 𝕜]
variable (X : Type u) (Y : Type v)
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem banachMazurDistance_le_iff_approximate_isomorphic_bound
    {C : ℝ} (hC : 0 ≤ C) :
    banachMazurDistance 𝕜 X Y ≤ ENNReal.ofReal C ↔
      ∀ ε : ℝ, 0 < ε → IsomorphicWithBound 𝕜 X Y (C + ε) := by
  constructor
  · intro h ε hε
    apply isomorphicWithBound_of_banachMazurDistance_lt
    apply h.trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC).2 (by linarith)
  · intro h
    have hfinite : banachMazurDistance 𝕜 X Y ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((h 1 zero_lt_one).banachMazurDistance_le 𝕜 X Y)
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hC]
    apply le_of_forall_pos_le_add
    intro ε hε
    have hb := (h ε hε).banachMazurDistance_le 𝕜 X Y
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [ENNReal.toReal_ofReal (add_nonneg hC hε.le)] using hr

end ThesisCommon
