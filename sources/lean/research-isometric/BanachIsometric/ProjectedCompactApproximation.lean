import BanachIsometric.ContinuousCompactApproximation
import BanachIsometric.LocalIsometricFrames
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Projected Lipschitz approximation of an actual continuous section

First approximate the continuous ambient operator map on the actual compact
parameter set. Projection into the prescribed subspace preserves the required
range inclusion and does not increase the approximation error. Compactness
and the original projection Lipschitz estimate give a genuine global operator
Lipschitz bound for the projected approximation.
-/

namespace BanachIsometric

open Set
open scoped Topology NNReal

noncomputable section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_projected_lipschitz_approximation_on_compact
    {s : Set P} (hs : IsCompact s) (A : C(s, E →L[ℝ] F))
    (H : s → Submodule ℝ F) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a ↦ (H a).starProjection))
    (hRange : ∀ a : s, ∀ x : E, A a x ∈ H a) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : s → E →L[ℝ] F, ∃ LY : ℝ≥0,
      LipschitzWith LY Y ∧ (∀ a : s, ∀ x : E, Y a x ∈ H a) ∧
      (∀ a : s, dist (Y a) (A a) < ε) := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  obtain ⟨B, LB, hBLipAmbient, hBclose⟩ := exists_lipschitz_approximation_on_compact hs A hε
  have hBLip : LipschitzWith LB (fun a : s ↦ B a.val) := hBLipAmbient.lipschitzOnWith.to_restrict
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set s)).exists_bound_of_continuousOn
    hBLip.continuous.continuousOn
  let Mn : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  let Y : s → E →L[ℝ] F := fun a ↦ (H a).starProjection.comp (B a.val)
  have hYLip : LipschitzOnWith ((1 : ℝ≥0) * LB + LP * Mn) Y univ :=
    lipschitzOnWith_clm_comp (MA := 1) (MB := Mn)
      hProj.lipschitzOnWith hBLip.lipschitzOnWith
      (fun a _ ↦ (H a).starProjection_norm_le)
      (fun a _ ↦ (hM a (mem_univ a)).trans (le_max_left _ _))
  have hfix : ∀ a : s, (H a).starProjection.comp (A a) = A a := by
    intro a
    ext x
    exact (H a).starProjection_eq_self_iff.mpr (hRange a x)
  refine ⟨Y, (1 : ℝ≥0) * LB + LP * Mn, lipschitzOnWith_univ.mp hYLip, ?_, ?_⟩
  · intro a x
    exact (H a).starProjection_apply_mem (B a.val x)
  · intro a
    have hdiff : Y a - A a = (H a).starProjection.comp (B a.val - A a) := by
      rw [ContinuousLinearMap.comp_sub, hfix a]
    calc
      dist (Y a) (A a) = ‖(H a).starProjection.comp (B a.val - A a)‖ := by
        rw [dist_eq_norm, hdiff]
      _ ≤ ‖(H a).starProjection‖ * ‖B a.val - A a‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖B a.val - A a‖ :=
        mul_le_mul_of_nonneg_right (H a).starProjection_norm_le (norm_nonneg _)
      _ = ‖B a.val - A a‖ := one_mul _
      _ < ε := by simpa only [dist_eq_norm] using hBclose a

end

end BanachIsometric
