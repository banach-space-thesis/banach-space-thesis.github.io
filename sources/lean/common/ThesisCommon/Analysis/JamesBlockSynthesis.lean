import ThesisCommon.Analysis.JamesFiniteBlocks
import ThesisCommon.Analysis.JamesDisjointEstimate
import ThesisCommon.Analysis.LpFamilySynthesis

/-! Bounded synthesis from the genuine dependent lp-sum of consecutive
finite James blocks. The norm bound is two, uniformly in all block lengths. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] (p : BanachExponent) (hp : p.val ≠ ∞)
  (σ : ℕ → ℕ) (hσ : StrictMono σ)

abbrev JamesBlockSum := lp (fun i : ℕ => JamesIntervalBlock 𝕜 p (σ i) (σ (i + 1))) p.val

include hσ in
theorem james_blocks_disjoint (F : Finset ℕ)
    (x : ∀ i : ℕ, JamesIntervalBlock 𝕜 p (σ i) (σ (i + 1))) (k : ℕ) :
    (F.filter (fun i => (x i).val k ≠ 0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hili : σ i < k := lt_of_not_ge (fun h => hi' ((x i).property k (Or.inl h)))
  have hiri : k < σ (i + 1) := lt_of_not_ge (fun h => hi' ((x i).property k (Or.inr h)))
  have hilj : σ j < k := lt_of_not_ge (fun h => hj' ((x j).property k (Or.inl h)))
  have hirj : k < σ (j + 1) := lt_of_not_ge (fun h => hj' ((x j).property k (Or.inr h)))
  rcases lt_trichotomy i j with h | h | h
  · have hij : σ (i + 1) ≤ σ j := hσ.monotone (by omega)
    omega
  · exact h
  · have hji : σ (j + 1) ≤ σ i := hσ.monotone (by omega)
    omega

include hp hσ in
theorem james_blocks_finite_synthesis_bound (F : Finset ℕ)
    (x : ∀ i : ℕ, JamesIntervalBlock 𝕜 p (σ i) (σ (i + 1))) :
    ‖∑ i ∈ F, (x i).val‖ ≤ 2 * ‖∑ i ∈ F, lp.single p.val i (x i)‖ := by
  have hq : 0 < p.val.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _)) hq).mp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _), lp.norm_sum_single hq]
  apply (james_disjoint_norm_rpow_le p hp F (fun i => (x i).val)
    (james_blocks_disjoint p σ hσ F x)).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith))
    (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))

def jamesBlockSynthesis : JamesBlockSum (𝕜 := 𝕜) p σ →L[𝕜] JamesSequenceSpace 𝕜 p :=
  lpFamilySynthesis hp (fun i => (jamesIntervalSubmodule 𝕜 p (σ i) (σ (i + 1))).subtypeL)
    (by norm_num : (0 : ℝ) ≤ 2) (james_blocks_finite_synthesis_bound p hp σ hσ)

theorem jamesBlockSynthesis_norm_le : ‖jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ‖ ≤ 2 :=
  norm_lpFamilySynthesis_le hp _ _ _

@[simp] theorem jamesBlockSynthesis_single (i : ℕ)
    (x : JamesIntervalBlock 𝕜 p (σ i) (σ (i + 1))) :
    jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ (lp.single p.val i x) = x.val :=
  lpFamilySynthesis_single hp
    (fun i => (jamesIntervalSubmodule 𝕜 p (σ i) (σ (i + 1))).subtypeL)
    (by norm_num : (0 : ℝ) ≤ 2) (james_blocks_finite_synthesis_bound p hp σ hσ) i x

include hp hσ in
theorem jamesBlockSynthesis_summable (x : JamesBlockSum (𝕜 := 𝕜) p σ) :
    Summable (fun i => (x i).val) :=
  summable_lp_family_of_finite_bound hp
    (fun i => (jamesIntervalSubmodule 𝕜 p (σ i) (σ (i + 1))).subtypeL)
    (by norm_num : (0 : ℝ) ≤ 2) (james_blocks_finite_synthesis_bound p hp σ hσ) x

theorem jamesBlockSynthesis_apply (x : JamesBlockSum (𝕜 := 𝕜) p σ) :
    jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ x = ∑' i, (x i).val := rfl

theorem jamesBlockSynthesis_endpoint (x : JamesBlockSum (𝕜 := 𝕜) p σ) (n : ℕ) :
    jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ x (σ n) = 0 := by
  have hz (i : ℕ) : (x i).val (σ n) = 0 := by
    rcases le_or_gt n i with h | h
    · exact (x i).property (σ n) (Or.inl (hσ.monotone h))
    · exact (x i).property (σ n) (Or.inr (hσ.monotone (by omega)))
  change JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) (σ n)
    (jamesBlockSynthesis (𝕜 := 𝕜) p hp σ hσ x) = 0
  rw [jamesBlockSynthesis_apply,
    (JamesSequenceSpace.coordinate (𝕜 := 𝕜) (p := p) (σ n)).map_tsum
      (jamesBlockSynthesis_summable p hp σ hσ x)]
  simpa only [JamesSequenceSpace.coordinate_apply, hz] using (tsum_zero : (∑' _ : ℕ, (0 : 𝕜)) = 0)

end ThesisCommon
