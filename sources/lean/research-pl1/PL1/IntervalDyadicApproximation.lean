import PL1.DyadicTrace
import PL1.StrongConvergence
import PL1.PartitionAverages
import PL1.TraceDomination

/-! # Geometry and approximation by the concrete dyadic interval partitions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology BoundedContinuousFunction

namespace PL1.DyadicTrace

attribute [local instance] intervalMeasure_probability

theorem index_succ_div (n : ℕ) (x : ℝ) : index (n + 1) x / 2 = index n x := by
  unfold index
  have hfloor : ⌊(2 : ℝ) ^ (n + 1) * x⌋₊ / 2 = ⌊(2 : ℝ) ^ n * x⌋₊ := by
    rw [show (2 : ℝ) ^ (n + 1) * x = (2 ^ n * x) * 2 by rw [pow_succ]; ring]
    exact Nat.mul_cast_floor_div_cancel (by decide : (2 : ℕ) ≠ 0) _
  have hcap : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
    rw [pow_succ]
    have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
    omega
  omega

theorem cell_refine (n i : ℕ) : cell n i = cell (n + 1) (2 * i) ∪ cell (n + 1) (2 * i + 1) := by
  ext x
  have h := index_succ_div n x
  simp only [cell, Set.mem_ofPred_eq, Set.mem_union]
  omega

theorem index_location (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (index n x : ℝ) ≤ (2 : ℝ) ^ n * x ∧
      (2 : ℝ) ^ n * x ≤ (index n x : ℝ) + 1 := by
  have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hfloor := Nat.floor_le (mul_nonneg hpos.le hx.1)
  have hil : index n x ≤ ⌊(2 : ℝ) ^ n * x⌋₊ := min_le_left _ _
  have hil' : (index n x : ℝ) ≤ (⌊(2 : ℝ) ^ n * x⌋₊ : ℝ) := by exact_mod_cast hil
  refine ⟨hil'.trans hfloor, ?_⟩
  by_cases hi : ⌊(2 : ℝ) ^ n * x⌋₊ ≤ 2 ^ n - 1
  · rw [index, min_eq_left hi]
    exact (Nat.lt_floor_add_one _).le
  · rw [index, min_eq_right (le_of_lt (lt_of_not_ge hi))]
    have hn : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by decide))
    have hcast : ((2 ^ n - 1 : ℕ) : ℝ) + 1 = (2 : ℝ) ^ n := by
      rw [Nat.cast_sub hn, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      ring
    rw [hcast]
    exact mul_le_of_le_one_right hpos.le hx.2

theorem dist_le_mesh (n i : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hxi : x ∈ cell n i) (hyi : y ∈ cell n i) : dist x y ≤ (2 : ℝ)⁻¹ ^ n := by
  have hxl := index_location n x hx
  have hyl := index_location n y hy
  change index n x = i at hxi
  change index n y = i at hyi
  rw [hxi] at hxl
  rw [hyi] at hyl
  have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  rw [Real.dist_eq, abs_le, inv_pow]
  constructor
  · have h := (le_div_iff₀ hpos).mpr (show (y - x) * 2 ^ n ≤ 1 by nlinarith)
    rw [one_div] at h
    linarith
  · rw [← one_div]
    apply (le_div_iff₀ hpos).mpr
    nlinarith

theorem left_mem_interval (n i : ℕ) (hi : i < 2 ^ n) :
    (i : ℝ) / (2 : ℝ) ^ n ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  refine ⟨by positivity, (div_le_one hp).mpr ?_⟩
  exact_mod_cast hi.le

theorem index_left (n i : ℕ) (hi : i < 2 ^ n) :
    index n ((i : ℝ) / (2 : ℝ) ^ n) = i := by
  unfold index
  rw [mul_div_cancel₀ _ (pow_ne_zero n (by norm_num)), Nat.floor_natCast,
    min_eq_left (Nat.le_sub_one_of_lt hi)]

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev dyadicVector (n i : ℕ) : IntervalL1 𝕜 :=
  PartitionAverages.vector intervalMeasure (cell n) (measurableSet_cell n) i

def step (n : ℕ) (c : ℕ → 𝕜) : IntervalL1 𝕜 :=
  ∑ i ∈ Finset.range (2 ^ n), c i • dyadicVector (𝕜 := 𝕜) n i

theorem coeFn_step (n : ℕ) (c : ℕ → 𝕜) :
    step n c =ᵐ[intervalMeasure] (fun x => c (index n x)) := by
  refine (Lp.coeFn_fun_finsetSum (Finset.range (2 ^ n)) _).trans ?_
  filter_upwards [ae_all_iff.2 (fun i => Lp.coeFn_smul (c i) (dyadicVector (𝕜 := 𝕜) n i)),
    ae_all_iff.2 (fun i => indicatorConstLp_coeFn (p := 1) (hs := measurableSet_cell n i)
      (hμs := measure_ne_top intervalMeasure (cell n i)) (c := (1 : 𝕜)))] with x hs he
  rw [Finset.sum_eq_single (index n x)]
  · rw [hs (index n x)]
    change c (index n x) * dyadicVector (𝕜 := 𝕜) n (index n x) x = _
    rw [show dyadicVector (𝕜 := 𝕜) n (index n x) x = (cell n (index n x)).indicator (fun _ => (1 : 𝕜)) x
      from he (index n x), Set.indicator_of_mem (show x ∈ cell n (index n x) from rfl), mul_one]
  · intro i hi hix
    rw [hs i]
    change c i * dyadicVector (𝕜 := 𝕜) n i x = _
    rw [show dyadicVector (𝕜 := 𝕜) n i x = (cell n i).indicator (fun _ => (1 : 𝕜)) x from he i,
      Set.indicator_of_notMem (show x ∉ cell n i from fun h => hix h.symm), mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (index_lt n x))).elim

abbrev dyadicAverage (n : ℕ) : IntervalL1 𝕜 →L[𝕜] IntervalL1 𝕜 :=
  PartitionAverages.average intervalMeasure (cell n) (measurableSet_cell n) (Finset.range (2 ^ n))

theorem norm_dyadicAverage_le_one (n : ℕ) : ‖dyadicAverage (𝕜 := 𝕜) n‖ ≤ 1 :=
  PartitionAverages.norm_average_le_one _ _ _ _ (pairwiseDisjoint_cell n)

theorem dyadicAverage_step (n : ℕ) (c : ℕ → 𝕜) : dyadicAverage n (step n c) = step n c :=
  PartitionAverages.average_step _ _ _ _ (pairwiseDisjoint_cell n) c

theorem step_continuous_tendsto (f : ℝ →ᵇ 𝕜) :
    Tendsto (fun n => step n (fun i => f ((i : ℝ) / (2 : ℝ) ^ n))) atTop
      (𝓝 (BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).uniformContinuousOn_of_continuous
      f.continuous.continuousOn)
      (ε / 2) (half_pos hε)
  have hmesh : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hmem : ∀ᵐ x ∂intervalMeasure, x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have hb : ∀ᵐ x ∂intervalMeasure,
      ‖(step n (fun i => f ((i : ℝ) / (2 : ℝ) ^ n)) -
        BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f) x‖ ≤ ε / 2 := by
    filter_upwards [Lp.coeFn_sub (step n (fun i => f ((i : ℝ) / (2 : ℝ) ^ n)))
      (BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f), coeFn_step n
        (fun i => f ((i : ℝ) / (2 : ℝ) ^ n)), BoundedContinuousFunction.coeFn_toLp 1 intervalMeasure 𝕜 f,
      hmem] with x hsub hs hf hx
    rw [hsub, Pi.sub_apply, hs, hf]
    have hleft := left_mem_interval n (index n x) (index_lt n x)
    have hdist := dist_le_mesh n (index n x) hleft hx
      (index_left n (index n x) (index_lt n x)) rfl
    simpa only [dist_eq_norm] using (hfδ _ hleft x hx (hdist.trans_lt (hN n hn))).le
  have hnorm := Lp.norm_le_of_ae_bound (half_pos hε).le hb
  have hnorm' : ‖step n (fun i => f ((i : ℝ) / (2 : ℝ) ^ n)) -
      BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f‖ ≤ ε / 2 := by
        simpa [measureUnivNNReal] using hnorm
  exact hnorm'.trans_lt (half_lt_self hε)

set_option backward.isDefEq.respectTransparency false in
theorem dyadicAverage_continuous_tendsto (f : ℝ →ᵇ 𝕜) :
    Tendsto (fun n => dyadicAverage n (BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f))
      atTop (𝓝 (BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f)) := by
  let F := BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 f
  let v : ℕ → IntervalL1 𝕜 := fun n => step n (fun i => f ((i : ℝ) / (2 : ℝ) ^ n))
  have hv : Tendsto v atTop (𝓝 F) := step_continuous_tendsto f
  have hb (n : ℕ) : ‖dyadicAverage n F - F‖ ≤ 2 * ‖v n - F‖ := by
    have heq : dyadicAverage n F - F = dyadicAverage n (F - v n) + (v n - F) := by
      rw [map_sub, show dyadicAverage n (v n) = v n from dyadicAverage_step n _]
      abel
    rw [heq]
    calc
      _ ≤ ‖dyadicAverage n (F - v n)‖ + ‖v n - F‖ := norm_add_le _ _
      _ ≤ ‖F - v n‖ + ‖v n - F‖ := by
          have hnorm : ‖dyadicAverage n (F - v n)‖ ≤ ‖F - v n‖ := by
            calc
              ‖dyadicAverage n (F - v n)‖ ≤ ‖dyadicAverage (𝕜 := 𝕜) n‖ * ‖F - v n‖ :=
                ContinuousLinearMap.le_opNorm (dyadicAverage (𝕜 := 𝕜) n) (F - v n)
              _ ≤ 1 * ‖F - v n‖ := mul_le_mul_of_nonneg_right
                (norm_dyadicAverage_le_one (𝕜 := 𝕜) n) (norm_nonneg _)
              _ = ‖F - v n‖ := one_mul _
          linarith
      _ = 2 * ‖v n - F‖ := by rw [norm_sub_rev F (v n)]; ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hzero : Tendsto (fun n => 2 * ‖v n - F‖) atTop (𝓝 0) := by
    simpa using (hv.sub_const F).norm.const_mul 2
  exact squeeze_zero (fun _ => norm_nonneg _) hb hzero

theorem dyadicAverage_tendsto (f : IntervalL1 𝕜) :
    Tendsto (fun n => dyadicAverage n f) atTop (𝓝 f) := by
  have hclosed := isClosed_convergenceSubmodule (dyadicAverage (𝕜 := 𝕜))
    (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜)) atTop 1 norm_dyadicAverage_le_one
  have hsubset : Set.range (BoundedContinuousFunction.toLp 1 intervalMeasure 𝕜 :
      (ℝ →ᵇ 𝕜) →L[𝕜] IntervalL1 𝕜) ⊆
      convergenceSubmodule (dyadicAverage (𝕜 := 𝕜)) (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜)) atTop := by
    rintro g ⟨v, rfl⟩
    exact dyadicAverage_continuous_tendsto v
  have hdense := BoundedContinuousFunction.toLp_denseRange 𝕜 intervalMeasure 𝕜 (p := 1) (by norm_num)
  exact hclosed.closure_subset_iff.mpr hsubset (hdense f)

theorem dyadicVector_refine (n i : ℕ) :
    dyadicVector (𝕜 := 𝕜) n i = dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i) +
      dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i + 1) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i))
    (dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i + 1)),
    indicatorConstLp_coeFn (p := 1) (hs := measurableSet_cell n i)
      (hμs := measure_ne_top intervalMeasure (cell n i)) (c := (1 : 𝕜)),
    indicatorConstLp_coeFn (p := 1) (hs := measurableSet_cell (n + 1) (2 * i))
      (hμs := measure_ne_top intervalMeasure (cell (n + 1) (2 * i))) (c := (1 : 𝕜)),
    indicatorConstLp_coeFn (p := 1) (hs := measurableSet_cell (n + 1) (2 * i + 1))
      (hμs := measure_ne_top intervalMeasure (cell (n + 1) (2 * i + 1))) (c := (1 : 𝕜))]
      with x hadd hp h0 h1
  change dyadicVector (𝕜 := 𝕜) n i x = _
  rw [hadd]
  change dyadicVector (𝕜 := 𝕜) n i x = dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i) x +
    dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i + 1) x
  rw [show dyadicVector (𝕜 := 𝕜) n i x = _ from hp,
    show dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i) x = _ from h0,
    show dyadicVector (𝕜 := 𝕜) (n + 1) (2 * i + 1) x = _ from h1,
    cell_refine]
  have hdisj : Disjoint (cell (n + 1) (2 * i)) (cell (n + 1) (2 * i + 1)) :=
    pairwiseDisjoint_cell (n + 1) (by omega)
  exact congrFun (Set.indicator_union_of_disjoint hdisj (fun _ => (1 : 𝕜))) x

theorem sum_norm_dyadicVector (n : ℕ) :
    (∑ i ∈ Finset.range (2 ^ n), ‖dyadicVector (𝕜 := 𝕜) n i‖) = 1 := by
  simp only [dyadicVector, PartitionAverages.norm_vector]
  rw [← measureReal_biUnion_finset (fun i _ j _ hij => pairwiseDisjoint_cell n hij)
    (fun i _ => measurableSet_cell n i) (fun i _ => measure_ne_top intervalMeasure (cell n i)), cover_cell]
  simp

/-- The full trace-dominator lemma, for arbitrary real or complex operators
and arbitrary (possibly infinite) target measure. -/
theorem exists_integrable_dominator {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : IntervalL1 𝕜 →L[𝕜] Lp 𝕜 1 μ) :
    ∃ G : Ω → ℝ, Integrable G μ ∧ (∀ x, 0 ≤ G x) ∧ (∫ x, G x ∂μ) ≤ ‖B‖ ∧
      ∀ f : Lp 𝕜 ∞ intervalMeasure, ‖f‖ ≤ 1 →
        ∀ᵐ x ∂μ, ‖B (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top f) x‖ ≤ G x := by
  let U : Set (IntervalL1 𝕜) := {g | ∃ f : Lp 𝕜 ∞ intervalMeasure,
    ‖f‖ ≤ 1 ∧ ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top f = g}
  have happrox : ∀ g ∈ U, ∃ c : ℕ → ℕ → 𝕜, (∀ n i, ‖c n i‖ ≤ 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.range (2 ^ n), c n i • dyadicVector (𝕜 := 𝕜) n i)
        atTop (𝓝 g) := by
    rintro g ⟨f, hf, rfl⟩
    refine ⟨fun n i => PartitionAverages.coefficient intervalMeasure (cell n) (measurableSet_cell n) i
      (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top f), ?_, ?_⟩
    · intro n i
      exact PartitionAverages.norm_coefficient_inclusion_le_one _ _ _ i f hf
    · simpa only [dyadicAverage, PartitionAverages.average_apply] using
        dyadicAverage_tendsto (ProbabilityLp.inclusion intervalMeasure 1 ∞ le_top f)
  obtain ⟨G, hG, hGpos, hGint, hGU⟩ := TraceDomination.exists_dominator_of_binary_approximation μ
    (dyadicVector (𝕜 := 𝕜)) B (fun n i _ => dyadicVector_refine n i)
    (fun n => (sum_norm_dyadicVector (𝕜 := 𝕜) n).le) U happrox
  exact ⟨G, hG, hGpos, hGint, fun f hf => hGU _ ⟨f, hf, rfl⟩⟩

end PL1.DyadicTrace

