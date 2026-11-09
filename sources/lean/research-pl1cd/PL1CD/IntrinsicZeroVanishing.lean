import PL1CD.ScalarOperatorVanishing
import PL1CD.VariationComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology NNReal

namespace PL1CD.Variation
open PL1 PL1.Noise PL1.ResolventEstimates PL1CD.PositiveHaarOperators

theorem seminorm_tsum_zero {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
    (p : Seminorm K E) (hp : Continuous p) (f : ℕ → E)
    (hf : Summable f) (hz : ∀ j, p (f j) = 0) : p (∑' j, f j) = 0 := by
  classical
  have hfinite (s : Finset ℕ) : p (∑ j ∈ s, f j) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      apply le_antisymm _ (apply_nonneg _ _)
      exact (map_add_le_add p _ _).trans (by rw [hz, ih]; simp)
  have ht := (hp.tendsto _).comp hf.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique ht (by
    simpa only [Function.comp_def, hfinite] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

variable {K Y : Type*} [RCLike K] [NormedAddCommGroup Y] [NormedSpace K Y]

theorem baseColumn_norm_le_geometric (S : DyadicSystem K Y) (j : ℕ) :
    ‖S.baseColumn j‖ ≤ dyadicRatio ^ j := by
  cases j with
  | zero => simpa only [DyadicSystem.baseColumn, synthesisCoordinate, pow_zero]
      using S.contractive 0
  | succ j =>
    rw [DyadicSystem.baseColumn, synthesisCoordinate, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (pow_nonneg dyadicRatio_nonneg _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (S.contractive j)
      (pow_nonneg dyadicRatio_nonneg (j + 1))

theorem norm_intrinsic_coord_le_one (S : DyadicSystem K Y) (j : ℕ) :
    ‖IntrinsicGraph.coord S.analysis j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x : PL1.L1Sum Y) j‖ ≤ 1 * ‖x‖
  simpa only [one_mul, Submodule.coe_norm] using
    lp.norm_apply_le_norm (by simp) (x : PL1.L1Sum Y) j

variable (K : Type*) [RCLike K]

theorem intrinsic_evalZero_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (T : HaarL1 K →L[K] (dyadicSystem K rates).IntrinsicSpace) :
    averagedVariation K (HaarL1 K) M N H hH
      ((IntrinsicGraph.evalZero (dyadicSystem K rates).analysis).comp T) = 0 := by
  let S := dyadicSystem K rates
  let U : ℕ → HaarL1 K →L[K] HaarL1 K := fun j =>
    (IntrinsicGraph.coord S.analysis j).comp T
  let V : ℕ → HaarL1 K →L[K] HaarL1 K := fun j => (S.baseColumn j).comp (U j)
  have hU (j : ℕ) : ‖U j‖ ≤ ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_intrinsic_coord_le_one S j) (norm_nonneg T))
  have hn (j : ℕ) : ‖V j‖ ≤ dyadicRatio ^ j * ‖T‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (baseColumn_norm_le_geometric S j) (hU j)
        (norm_nonneg _) (pow_nonneg dyadicRatio_nonneg _))
  have hs : Summable V :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn
      (geometric_summable.mul_right ‖T‖)).of_norm
  have he : (IntrinsicGraph.evalZero S.analysis).comp T = ∑' j, V j := by
    apply ContinuousLinearMap.ext
    intro f
    have hv := (ContinuousLinearMap.apply K (HaarL1 K) f).map_tsum hs
    change (∑' j, V j) f = ∑' j, V j f at hv
    rw [hv]
    have hr := congrArg (IntrinsicGraph.evalZero S.analysis) (S.reconstruction_inclusion (T f))
    rw [S.evalZero_reconstruction] at hr
    exact hr.symm
  rw [he]
  apply seminorm_tsum_zero _ (averagedVariation_continuous K (HaarL1 K) M N H hH) V hs
  intro j
  cases j with
  | zero => exact scalar_resolvent_vanishing K rates M N H hH hgrowth (dyadicTime 0) (U 0)
  | succ j =>
    change averagedVariation K (HaarL1 K) M N H hH
      ((((dyadicRatio ^ (j + 1) : ℝ) : K) • resolventL1 K rates (dyadicTime j)).comp (U (j + 1))) = 0
    rw [ContinuousLinearMap.smul_comp, map_smul_eq_mul,
      scalar_resolvent_vanishing K rates M N H hH hgrowth, mul_zero]

theorem intrinsic_coordinate_vanishing
    (rates : ℕ → ℝ≥0) (M N : ℕ → ℕ) (H : Set ℕ) (hH : H.Infinite)
    (hgrowth : GrowthCriterion rates M N H)
    (T : HaarL1 K →L[K] (dyadicSystem K rates).IntrinsicSpace) (i : ℕ) :
    averagedVariation K (HaarL1 K) M N H hH
      ((IntrinsicGraph.coord (dyadicSystem K rates).analysis i).comp T) = 0 := by
  let S := dyadicSystem K rates
  have he : (IntrinsicGraph.coord S.analysis i).comp T =
      (S.analysis i).comp ((IntrinsicGraph.evalZero S.analysis).comp T) := by
    apply ContinuousLinearMap.ext
    intro f
    exact IntrinsicGraph.coord_eq S.analysis i (T f)
  rw [he]
  apply le_antisymm _ (apply_nonneg _ _)
  exact (averagedVariation_comp_le M N H hH _ (S.analysis i)).trans (by
    rw [intrinsic_evalZero_vanishing K rates M N H hH hgrowth T, mul_zero])

end PL1CD.Variation
