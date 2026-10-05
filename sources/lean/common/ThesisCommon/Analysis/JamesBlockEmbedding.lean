import ThesisCommon.Analysis.JamesBlockSynthesis
import ThesisCommon.Analysis.JamesFiniteBlockLower

/-! The block synthesis is bounded below, and therefore has closed range.
Both bounds use the inherited James norms on the actual finite intervals. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (σ : ℕ → ℕ) (hσ : StrictMono σ)

theorem jamesBlockSynthesis_finite_norm_ge (x : JamesBlockSum (𝕜 := 𝕜) p σ) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, lp.single p.val i (x i)‖ ≤
      ‖jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ
        (∑ i ∈ Finset.range N, lp.single p.val i (x i))‖ := by
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hq).mp
  rw [lp.norm_sum_single hq, map_sum]
  simp only [jamesBlockSynthesis_single]
  have h := james_finite_blocks_lower p hp σ hσ (fun i : Fin N => x i.val)
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖x i‖ ^ p.val.toReal),
    Fin.sum_univ_eq_sum_range (fun i => (x i).val)] at h
  exact h

theorem jamesBlockSynthesis_norm_ge (x : JamesBlockSum (𝕜 := 𝕜) p σ) :
    ‖x‖ ≤ ‖jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ x‖ := by
  have ht := (lp.hasSum_single hp x).tendsto_sum_nat
  exact le_of_tendsto_of_tendsto ht.norm
    (((jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ).continuous.tendsto x).comp ht).norm
    (Eventually.of_forall (jamesBlockSynthesis_finite_norm_ge p hp σ hσ x))

theorem jamesBlockSynthesis_injective :
    Function.Injective (jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ) := by
  intro x y h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hb := jamesBlockSynthesis_norm_ge p hp σ hσ (x - y)
  simpa only [map_sub, h, sub_self, norm_zero] using hb

theorem jamesBlockSynthesis_range_isClosed :
    IsClosed (Set.range (jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ)) := by
  apply ((jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ).antilipschitz_of_bound
    (K := 1) (fun x => by simpa only [NNReal.coe_one, one_mul] using
      jamesBlockSynthesis_norm_ge p hp σ hσ x)).isClosed_range
  exact (jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ).uniformContinuous

end ThesisCommon
