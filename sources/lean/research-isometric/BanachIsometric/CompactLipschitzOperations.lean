import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! Products of actual Lipschitz scalar and vector maps on a compact source
are Lipschitz. The needed bounds are proved by compactness. -/

namespace BanachIsometric

open Set
open scoped NNReal

theorem exists_lipschitz_smul_of_compact
    {X V : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : X → ℝ} {u : X → V} {Ca Cu : ℝ≥0}
    (ha : LipschitzWith Ca a) (hu : LipschitzWith Cu u) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => a x • u x) := by
  obtain ⟨Ra, hRa⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_bound_of_continuousOn
    ha.continuous.continuousOn
  obtain ⟨Ru, hRu⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_bound_of_continuousOn
    hu.continuous.continuousOn
  let Ma : ℝ≥0 := ⟨max Ra 0, le_max_right _ _⟩
  let Mu : ℝ≥0 := ⟨max Ru 0, le_max_right _ _⟩
  have hMa (x : X) : ‖a x‖ ≤ Ma := (hRa x (mem_univ x)).trans (le_max_left _ _)
  have hMu (x : X) : ‖u x‖ ≤ Mu := (hRu x (mem_univ x)).trans (le_max_left _ _)
  refine ⟨Ma * Cu + Ca * Mu, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have hdec : a x • u x - a y • u y = a x • (u x - u y) + (a x - a y) • u y := by
    rw [smul_sub, sub_smul]
    abel
  have had : ‖a x - a y‖ ≤ (Ca : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using ha.dist_le_mul x y
  have hud : ‖u x - u y‖ ≤ (Cu : ℝ) * dist x y := by
    simpa only [dist_eq_norm] using hu.dist_le_mul x y
  rw [dist_eq_norm, hdec]
  calc
    ‖a x • (u x - u y) + (a x - a y) • u y‖ ≤
        ‖a x‖ * ‖u x - u y‖ + ‖a x - a y‖ * ‖u y‖ := by
      simpa only [norm_smul] using norm_add_le (a x • (u x - u y)) ((a x - a y) • u y)
    _ ≤ (Ma : ℝ) * ((Cu : ℝ) * dist x y) + ((Ca : ℝ) * dist x y) * Mu :=
      add_le_add (mul_le_mul (hMa x) hud (norm_nonneg _) Ma.coe_nonneg)
        (mul_le_mul had (hMu y) (norm_nonneg _) (mul_nonneg Ca.coe_nonneg dist_nonneg))
    _ = _ := by push_cast; ring

end BanachIsometric
