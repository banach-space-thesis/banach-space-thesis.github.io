import BanachIsometric.ExactSectionPrincipalAction

/-!
# Lipschitz transitions on whole overlaps

On a compact parameter space, a chartwise Lipschitz operator family is bounded
by its value at the chart centre and the parameter diameter. The actual
transition `B_j A_i` is therefore Lipschitz on the whole overlap. The group
values are measured in their actual ambient operator norm.
-/

namespace BanachIsometric

open Set
open scoped NNReal

noncomputable section

section Bounds

variable {P G : Type*} [PseudoMetricSpace P] [CompactSpace P]
    [NormedAddCommGroup G]

theorem exists_norm_bound_of_lipschitzOn_compact_base
    {U : Set P} {f : P → G} {L : ℝ≥0} (hL : LipschitzOnWith L f U)
    (i : P) (hi : i ∈ U) : ∃ M : ℝ≥0, ∀ a ∈ U, ‖f a‖ ≤ M := by
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set P), Metric.diam_nonneg⟩
  refine ⟨‖f i‖₊ + L * D, ?_⟩
  intro a ha
  have hd : dist a i ≤ (D : ℝ) :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ a) (mem_univ i)
  have hdist : dist (f a) (f i) ≤ (L : ℝ) * D :=
    (hL.dist_le_mul a ha i hi).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  simpa only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm] using
    norm_le_norm_add_const_of_dist_le hdist

end Bounds

namespace ExactSectionAtlas

variable {P E F : Type*} [PseudoMetricSpace P] [CompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {K : Set F} {H : P → Submodule ℝ F}
    (Z : ExactSectionAtlas S K H)

theorem exists_lipschitz_transition (i j : P) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun a => ((Z.transition i j a).val : E →L[ℝ] E)) (Z.baseSet i ∩ Z.baseSet j) := by
  obtain ⟨KA, hA⟩ := Z.forward_lipschitz i
  obtain ⟨KB, hB⟩ := Z.inverse_lipschitz j
  obtain ⟨MA, hMA⟩ := exists_norm_bound_of_lipschitzOn_compact_base hA i (Z.mem_baseSet i)
  obtain ⟨MB, hMB⟩ := exists_norm_bound_of_lipschitzOn_compact_base hB j (Z.mem_baseSet j)
  have hRaw : LipschitzOnWith (MB * KA + KB * MA) (Z.transitionOperator i j)
      (Z.baseSet i ∩ Z.baseSet j) :=
    lipschitzOnWith_clm_comp (hB.mono inter_subset_right) (hA.mono inter_subset_left)
      (fun a ha => hMB a ha.2) (fun a ha => hMA a ha.1)
  refine ⟨MB * KA + KB * MA, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb
  simpa only [Z.transition_val i j a ha, Z.transition_val i j b hb] using
    hRaw.dist_le_mul a ha b hb

theorem exists_finite_lipschitz_principal_atlas :
    ∃ I : Finset P, ∃ L : ℝ≥0,
      (∀ a : P, ∃ i ∈ I, a ∈ Z.baseSet i) ∧
      (∀ i ∈ I, LipschitzOnWith L (Z.forward i) (Z.baseSet i) ∧
        LipschitzOnWith L (Z.inverse i) (Z.baseSet i)) ∧
      ∀ i ∈ I, ∀ j ∈ I, ∃ C : ℝ≥0, LipschitzOnWith C
        (fun a => ((Z.transition i j a).val : E →L[ℝ] E)) (Z.baseSet i ∩ Z.baseSet j) := by
  obtain ⟨I, L, hcover, hLip⟩ := Z.exists_finite_uniform_lipschitz_atlas
  exact ⟨I, L, hcover, hLip, fun i _ j _ => Z.exists_lipschitz_transition i j⟩

end ExactSectionAtlas

end
end BanachIsometric
