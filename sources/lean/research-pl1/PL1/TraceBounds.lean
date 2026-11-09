import PL1.WalshModel
import PL1.L1Masks
import PL1.LpInclusions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Finite partition traces and the L-infinity to L1 norm bound -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace PL1.TraceBounds

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem integral_scalar_sign_mul (i j : ℕ) :
    (∫ x, Walsh.scalarCharacter 𝕜 {i} x * Walsh.scalarCharacter 𝕜 {j} x ∂Walsh.haar) =
      if i = j then 1 else 0 := by
  calc
    _ = ((∫ x, Walsh.character {i} x * Walsh.character {j} x ∂Walsh.haar : ℝ) : 𝕜) := by
      simp only [Walsh.scalarCharacter, ← RCLike.ofReal_mul, integral_ofReal]
    _ = _ := by rw [Walsh.integral_character_mul]; split_ifs <;> simp_all

private theorem scalar_sign_integrable (i j : ℕ) (c : 𝕜) :
    Integrable (fun x => (Walsh.scalarCharacter 𝕜 {i} x *
      Walsh.scalarCharacter 𝕜 {j} x) * c) Walsh.haar :=
  ((Walsh.continuous_scalarCharacter 𝕜 {i}).mul
    (Walsh.continuous_scalarCharacter 𝕜 {j}) |>.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

section AbstractTrace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The diagonal sum associated with a finite family and finite tests. -/
def finiteTrace (s : Finset ℕ) (e : ℕ → E) (φ : ℕ → F →L[𝕜] 𝕜)
    (T : E →L[𝕜] F) : 𝕜 := ∑ i ∈ s, φ i (T (e i))

theorem finiteTrace_sub (s : Finset ℕ) (e : ℕ → E) (φ : ℕ → F →L[𝕜] 𝕜)
    (T U : E →L[𝕜] F) :
    finiteTrace s e φ (T - U) = finiteTrace s e φ T - finiteTrace s e φ U := by
  simp only [finiteTrace, sub_apply, map_sub, Finset.sum_sub_distrib]

theorem finiteTrace_eq_sign_average (s : Finset ℕ) (e : ℕ → E)
    (φ : ℕ → F →L[𝕜] 𝕜) (T : E →L[𝕜] F) :
    finiteTrace s e φ T = ∫ x,
      (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • φ i)
        (T (∑ j ∈ s, Walsh.scalarCharacter 𝕜 {j} x • e j)) ∂Walsh.haar := by
  simp only [sum_apply, map_sum, map_smul, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [integral_finsetSum]
  · unfold finiteTrace
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum s (fun j _ => scalar_sign_integrable i j (φ j (T (e i))))]
    simp only [integral_mul_const, integral_scalar_sign_mul]
    simp [hi]
  · intro i hi
    exact integrable_finsetSum _ (fun j _ => scalar_sign_integrable i j _)

/-- The sign averaging proof of the finite trace bound, over either field. -/
theorem norm_finiteTrace_le (s : Finset ℕ) (e : ℕ → E) (φ : ℕ → F →L[𝕜] 𝕜)
    (he : ∀ x : Walsh.Group, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • e i‖ ≤ 1)
    (hφ : ∀ x : Walsh.Group, ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • φ i‖ ≤ 1)
    (T : E →L[𝕜] F) : ‖finiteTrace s e φ T‖ ≤ ‖T‖ := by
  rw [finiteTrace_eq_sign_average]
  have h := norm_integral_le_of_norm_le_const (μ := Walsh.haar)
    (C := ‖T‖) (ae_of_all _ (fun x =>
      calc
        _ ≤ ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • φ i‖ *
            ‖T (∑ j ∈ s, Walsh.scalarCharacter 𝕜 {j} x • e j)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (‖T‖ * 1) := mul_le_mul (hφ x)
          ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (he x) (norm_nonneg _)))
          (norm_nonneg _) zero_le_one
        _ = ‖T‖ := by ring))
  simpa using h

end AbstractTrace

section MeasurablePartition

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (A : ℕ → Set Ω) (hA : ∀ i, MeasurableSet (A i))

/-- A partition cell as an actual L-infinity class. -/
def cellVector (i : ℕ) : Lp 𝕜 ∞ μ :=
  indicatorConstLp ∞ (hA i) (measure_ne_top μ (A i)) (1 : 𝕜)

/-- Integration over a cell, as a bounded linear functional on actual L1. -/
def cellFunctional (i : ℕ) : Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  (L1.integralCLM' 𝕜).comp (L1Masks.mask μ (A i) (hA i))

omit [IsProbabilityMeasure μ] in
theorem cellFunctional_apply (i : ℕ) (f : Lp 𝕜 1 μ) :
    cellFunctional (𝕜 := 𝕜) μ A hA i f = ∫ x in A i, f x ∂μ := by
  change L1.integralCLM' 𝕜 (L1Masks.mask μ (A i) (hA i) f) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  rw [integral_congr_ae (L1Masks.coeFn_mask μ (A i) (hA i) f), integral_indicator (hA i)]

omit [IsProbabilityMeasure μ] in
theorem norm_cellFunctional_apply_le_mask (i : ℕ) (f : Lp 𝕜 1 μ) :
    ‖cellFunctional (𝕜 := 𝕜) μ A hA i f‖ ≤ ‖L1Masks.mask μ (A i) (hA i) f‖ := by
  change ‖L1.integralCLM' 𝕜 (L1Masks.mask μ (A i) (hA i) f)‖ ≤ _
  rw [← L1.integral_eq']
  exact L1.norm_integral_le _

omit [IsProbabilityMeasure μ] in
theorem norm_sign_cellFunctional_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (x : Walsh.Group) :
    ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • cellFunctional (𝕜 := 𝕜) μ A hA i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, sum_apply]
  calc
    _ ≤ ∑ i ∈ s, ‖Walsh.scalarCharacter 𝕜 {i} x • cellFunctional (𝕜 := 𝕜) μ A hA i f‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ s, ‖cellFunctional (𝕜 := 𝕜) μ A hA i f‖ := by
      simp only [norm_smul, Walsh.norm_scalarCharacter, one_mul]
    _ ≤ ∑ i ∈ s, ‖L1Masks.mask μ (A i) (hA i) f‖ :=
      Finset.sum_le_sum (fun i _ => norm_cellFunctional_apply_le_mask μ A hA i f)
    _ ≤ ‖f‖ := L1Masks.sum_norm_mask_le μ s A hA hdisj f

omit [MeasurableSpace Ω] in
private theorem norm_sum_disjoint_indicator_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (c : ℕ → 𝕜)
    (hc : ∀ i, ‖c i‖ ≤ 1) (y : Ω) :
    ‖∑ i ∈ s, c i * (A i).indicator (fun _ => (1 : 𝕜)) y‖ ≤ 1 := by
  classical
  by_cases hy : ∃ i ∈ s, y ∈ A i
  · obtain ⟨i, hi, hyi⟩ := hy
    rw [Finset.sum_eq_single i]
    · simpa only [Set.indicator_of_mem hyi, mul_one] using hc i
    · intro j hj hji
      have hyj : y ∉ A j := fun hyj => Set.disjoint_left.mp (hdisj hji) hyj hyi
      simp [Set.indicator_of_notMem hyj]
    · exact fun h => (h hi).elim
  · have hzero : ∀ i ∈ s, y ∉ A i := by simpa using hy
    have hz : (∑ i ∈ s, c i * (A i).indicator (fun _ => (1 : 𝕜)) y) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem (hzero i hi), mul_zero]
    rw [hz, norm_zero]
    exact zero_le_one

set_option backward.isDefEq.respectTransparency false in
theorem norm_sign_cellVector_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (x : Walsh.Group) :
    ‖∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • cellVector (𝕜 := 𝕜) μ A hA i‖ ≤ 1 := by
  have hcoe : (fun y => (∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • cellVector (𝕜 := 𝕜) μ A hA i) y) =ᵐ[μ]
      (fun y => ∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x *
        (A i).indicator (fun _ => (1 : 𝕜)) y) := by
    refine (Lp.coeFn_fun_finsetSum s _).trans ?_
    filter_upwards [ae_all_iff.2 (fun i => Lp.coeFn_smul
      (Walsh.scalarCharacter 𝕜 {i} x) (cellVector (𝕜 := 𝕜) μ A hA i)),
      ae_all_iff.2 (fun i =>
        (indicatorConstLp_coeFn (p := ∞) (hs := hA i)
          (hμs := measure_ne_top μ (A i)) (c := (1 : 𝕜))))] with y hs hi
    apply Finset.sum_congr rfl
    intro i his
    rw [hs i]
    change Walsh.scalarCharacter 𝕜 {i} x * cellVector (𝕜 := 𝕜) μ A hA i y = _
    rw [show cellVector (𝕜 := 𝕜) μ A hA i y = (A i).indicator (fun _ => (1 : 𝕜)) y from hi i]
  have hn := Lp.norm_le_of_ae_bound
    (f := ∑ i ∈ s, Walsh.scalarCharacter 𝕜 {i} x • cellVector (𝕜 := 𝕜) μ A hA i)
    zero_le_one (hcoe.mono (fun y hy => by
    exact le_of_eq_of_le (congrArg norm hy) (norm_sum_disjoint_indicator_le A s hdisj _
      (fun i => (Walsh.norm_scalarCharacter 𝕜 {i} x).le) y)))
  simpa using hn

/-- The trace for an arbitrary finite measurable partition. -/
def partitionTrace (s : Finset ℕ) (R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) : 𝕜 :=
  finiteTrace s (cellVector (𝕜 := 𝕜) μ A hA) (cellFunctional (𝕜 := 𝕜) μ A hA)
    (R.comp (ProbabilityLp.inclusion μ 1 ∞ le_top))

theorem norm_partitionTrace_le (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) :
    ‖partitionTrace μ A hA s R‖ ≤ ‖R.comp (ProbabilityLp.inclusion μ 1 ∞ le_top)‖ :=
  norm_finiteTrace_le s (cellVector (𝕜 := 𝕜) μ A hA)
    (cellFunctional (𝕜 := 𝕜) μ A hA)
    (norm_sign_cellVector_le (𝕜 := 𝕜) μ A hA s hdisj)
    (norm_sign_cellFunctional_le (𝕜 := 𝕜) μ A hA s hdisj)
    (R.comp (ProbabilityLp.inclusion μ 1 ∞ le_top))

theorem inclusion_cellVector (i : ℕ) :
    ProbabilityLp.inclusion μ 1 ∞ le_top (cellVector (𝕜 := 𝕜) μ A hA i) =
      indicatorConstLp 1 (hA i) (measure_ne_top μ (A i)) (1 : 𝕜) := by
  apply Lp.ext
  exact (ProbabilityLp.coeFn_inclusion μ 1 ∞ le_top _).trans
    (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)

/-- This is the manuscript's sum of cell integrals of images of cell indicators. -/
theorem partitionTrace_eq (s : Finset ℕ) (R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) :
    partitionTrace μ A hA s R = ∑ i ∈ s,
      ∫ x in A i, R (indicatorConstLp 1 (hA i) (measure_ne_top μ (A i)) (1 : 𝕜)) x ∂μ := by
  simp only [partitionTrace, finiteTrace, ContinuousLinearMap.comp_apply,
    inclusion_cellVector, cellFunctional_apply]

theorem partitionTrace_sub (s : Finset ℕ) (R T : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ) :
    partitionTrace μ A hA s (R - T) =
      partitionTrace μ A hA s R - partitionTrace μ A hA s T := by
  simp only [partitionTrace, ContinuousLinearMap.sub_comp, finiteTrace_sub]

theorem partitionTrace_id (s : Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : (⋃ i ∈ s, A i) = Set.univ) :
    partitionTrace (𝕜 := 𝕜) μ A hA s (ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ)) = 1 := by
  rw [partitionTrace_eq]
  simp only [ContinuousLinearMap.id_apply]
  have hi (i : ℕ) : (∫ x in A i,
      indicatorConstLp 1 (hA i) (measure_ne_top μ (A i)) (1 : 𝕜) x ∂μ) =
      (μ.real (A i) : 𝕜) := by
    rw [integral_congr_ae (ae_restrict_of_ae indicatorConstLp_coeFn)]
    rw [setIntegral_indicator (hA i)]
    simp [Algebra.smul_def]
  simp_rw [hi]
  rw [← RCLike.ofReal_sum]
  have hm : ∑ i ∈ s, μ.real (A i) = 1 := by
    rw [← measureReal_biUnion_finset (fun i _ j _ hij => hdisj hij)
      (fun i _ => hA i) (fun i _ => measure_ne_top μ (A i)), hcover]
    simp
  rw [hm, RCLike.ofReal_one]

end MeasurablePartition

section PartitionSequence

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (A : ℕ → ℕ → Set Ω) (hA : ∀ n i, MeasurableSet (A n i)) (s : ℕ → Finset ℕ)
  (hdisj : ∀ n, Pairwise (fun i j => Disjoint (A n i) (A n j)))

include hdisj

/-- Vanishing traces force distance at least one from the identity in the
L-infinity to L1 norm. -/
theorem one_le_norm_id_sub_of_trace_tendsto_zero
    (hcover : ∀ n, (⋃ i ∈ s n, A n i) = Set.univ)
    (R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hR : Filter.Tendsto (fun n => partitionTrace μ (A n) (hA n) (s n) R)
      Filter.atTop (𝓝 0)) :
    1 ≤ ‖(ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ) - R).comp
      (ProbabilityLp.inclusion μ 1 ∞ le_top)‖ := by
  have ht : Filter.Tendsto (fun n =>
      ‖partitionTrace μ (A n) (hA n) (s n) (ContinuousLinearMap.id 𝕜 (Lp 𝕜 1 μ) - R)‖)
      Filter.atTop (𝓝 1) := by
    simpa only [partitionTrace_sub, partitionTrace_id μ _ _ _ (hdisj _) (hcover _),
      sub_zero, norm_one] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 1)).sub hR).norm
  exact le_of_tendsto ht (Filter.Eventually.of_forall (fun n =>
    norm_partitionTrace_le μ (A n) (hA n) (s n) (hdisj n) _))

/-- The trace-vanishing condition is preserved by approximation in the
L-infinity to L1 norm, the topology used in the matrix argument. -/
theorem trace_tendsto_zero_of_approximation
    (R : Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (T : ℕ → Lp 𝕜 1 μ →L[𝕜] Lp 𝕜 1 μ)
    (hT : ∀ m, Filter.Tendsto (fun n => partitionTrace μ (A n) (hA n) (s n) (T m))
      Filter.atTop (𝓝 0))
    (happrox : Filter.Tendsto (fun m => ‖(R - T m).comp
      (ProbabilityLp.inclusion μ 1 ∞ le_top)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => partitionTrace μ (A n) (hA n) (s n) R)
      Filter.atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := Filter.Eventually.exists
    (happrox.eventually (gt_mem_nhds (half_pos hε)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hT m) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have herr := norm_partitionTrace_le μ (A n) (hA n) (s n) (hdisj n) (R - T m)
  rw [partitionTrace_sub] at herr
  have hn' := hN n hn
  rw [dist_zero_right] at hn'
  have htri := norm_add_le
    (partitionTrace μ (A n) (hA n) (s n) R - partitionTrace μ (A n) (hA n) (s n) (T m))
    (partitionTrace μ (A n) (hA n) (s n) (T m))
  rw [sub_add_cancel] at htri
  linarith

end PartitionSequence

end PL1.TraceBounds

