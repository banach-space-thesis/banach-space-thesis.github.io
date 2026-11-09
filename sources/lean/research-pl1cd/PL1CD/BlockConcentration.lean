import PL1CD.StageBlockEvents
import PL1.KernelTranslations
import PL1.ExponentialTail

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace PL1CD.StageParameters

def blockCoordinates (d k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun j => d + j)

def blockEvent (s d : ℕ) : Set PL1.Walsh.Group :=
  {x | threshold s / 2 < blockAverage d (blockSize s) x}

theorem measurableSet_blockEvent (s d : ℕ) : MeasurableSet (blockEvent s d) :=
  measurableSet_lt measurable_const (continuous_blockAverage _ _).measurable

theorem dependsOn_blockEvent (s d : ℕ) :
    PL1.FiniteCoordinateKernels.DependsOn (blockCoordinates d (blockSize s)) (blockEvent s d) := by
  classical
  intro x y hxy
  have havg : blockAverage d (blockSize s) x = blockAverage d (blockSize s) y := by
    unfold blockAverage
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    unfold PL1.Carrier.coordinate
    rw [hxy _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)]
  simp only [blockEvent, Set.mem_ofPred_eq, havg]

theorem haar_blockEvent_le {s : ℕ} (hs : 0 < s) (d : ℕ) :
    PL1.Walsh.haar (blockEvent s d) ≤ ENNReal.ofReal (errorBound s) := by
  have hvar := variance_blockAverage_le PL1.Walsh.haar d (blockSize s)
    (fun i j hij => PL1.Carrier.covariance_coordinate_haar hij)
  apply (PL1.Carrier.measure_above_le PL1.Walsh.haar _
    (memLp_blockAverage _ _ _) (integral_blockAverage_haar _ _)
    (show 0 < threshold s / 2 by unfold threshold; positivity)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (blockSize s : ℝ)⁻¹ / (threshold s / 2) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 4 / ((blockSize s : ℝ) * threshold s ^ 2) := by ring
    _ ≤ errorBound s := chebyshev_ratio_le hs

theorem rates_on_block {s d : ℕ} (hs : 0 < s) (A : Set ℕ) (hsA : s ∈ A)
    (hd : dimension (s - 1) ≤ d) (hend : d + blockSize s ≤ dimension s)
    {j : ℕ} (hj : j < blockSize s) : rates A (d + j) = (low s : ℝ≥0) := by
  have heq := coordinateStage_of_stage hs (show dimension (s - 1) ≤ d + j by omega)
    (show d + j < dimension s by omega)
  simp [rates, heq, stageRate, hsA]

theorem integral_blockAverage_noise_block_ge {s d : ℕ} (hs : 0 < s)
    (A : Set ℕ) (hsA : s ∈ A) (hd : dimension (s - 1) ≤ d)
    (hend : d + blockSize s ≤ dimension s) (u : ℝ≥0) (hu : (u : ℝ) ≤ s) :
    threshold s ≤ ∫ x, blockAverage d (blockSize s) x ∂PL1.Noise.measure (rates A) u := by
  have hk : (0 : ℝ) < blockSize s := by exact_mod_cast blockSize_pos hs
  unfold blockAverage
  rw [integral_const_mul, integral_finsetSum]
  · calc
      _ ≥ (blockSize s : ℝ)⁻¹ * ∑ _j ∈ Finset.range (blockSize s), threshold s := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
        apply Finset.sum_le_sum
        intro j hj
        rw [PL1.Carrier.integral_coordinate_noise, PL1.Noise.bias,
          rates_on_block hs A hsA hd hend (Finset.mem_range.mp hj)]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg hu) (by positivity)
      _ = threshold s := by simp [hk.ne']
  · intro j _
    exact (PL1.Carrier.memLp_coordinate (PL1.Noise.measure (rates A) u) _ 2).integrable (by norm_num)

theorem noise_blockEvent_compl_le {s d : ℕ} (hs : 0 < s)
    (A : Set ℕ) (hsA : s ∈ A) (hd : dimension (s - 1) ≤ d)
    (hend : d + blockSize s ≤ dimension s) (u : ℝ≥0) (hu : (u : ℝ) ≤ s) :
    PL1.Noise.measure (rates A) u (blockEvent s d)ᶜ ≤ ENNReal.ofReal (errorBound s) := by
  have hvar := variance_blockAverage_le (PL1.Noise.measure (rates A) u) d (blockSize s)
    (fun i j hij => PL1.Carrier.covariance_coordinate_noise (rates A) u hij)
  have heq : (blockEvent s d)ᶜ = {x | blockAverage d (blockSize s) x ≤ threshold s / 2} := by
    ext x
    simp [blockEvent]
  rw [heq]
  apply (PL1.Carrier.measure_below_le (PL1.Noise.measure (rates A) u) _
    (memLp_blockAverage _ _ _) (integral_blockAverage_noise_block_ge hs A hsA hd hend u hu)
    (Real.exp_pos _) (by linarith : 2 * (threshold s / 2) ≤ threshold s)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (blockSize s : ℝ)⁻¹ / (threshold s / 2) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 4 / ((blockSize s : ℝ) * threshold s ^ 2) := by ring
    _ ≤ errorBound s := chebyshev_ratio_le hs

theorem timeMeasure_unit_Ici (s : ℝ≥0) :
    PL1.ExponentialTime.timeMeasure 1 (Ici s) = ENNReal.ofReal (Real.exp (-(s : ℝ))) := by
  let := PL1.ExponentialTime.isProbabilityMeasure_timeMeasure (by norm_num : (0 : ℝ) < 1)
  have h := PL1.ExponentialTime.integral_laplace_Ici (by norm_num : (0 : ℝ) < 1)
    0 le_rfl s
  simp only [mul_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one, inv_one,
    add_zero, measureReal_def, Measure.restrict_apply_univ] at h
  rw [← h, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem resolvent_blockEvent_compl_le {s d : ℕ} (hs : 0 < s)
    (A : Set ℕ) (hsA : s ∈ A) (hd : dimension (s - 1) ≤ d)
    (hend : d + blockSize s ≤ dimension s) :
    PL1.Noise.resolventMeasure (rates A) 1 (blockEvent s d)ᶜ ≤
      ENNReal.ofReal (errorBound s) + ENNReal.ofReal (Real.exp (-(s : ℝ))) := by
  let := PL1.ExponentialTime.isProbabilityMeasure_timeMeasure (by norm_num : (0 : ℝ) < 1)
  change (PL1.ExponentialTime.timeMeasure 1).bind (PL1.Noise.kernel (rates A)) _ ≤ _
  rw [Measure.bind_apply (measurableSet_blockEvent s d).compl
    (PL1.Noise.kernel (rates A)).aemeasurable]
  calc
    _ ≤ ∫⁻ u : ℝ≥0, ENNReal.ofReal (errorBound s) +
        (Ici (s : ℝ≥0)).indicator (fun _ => (1 : ℝ≥0∞)) u
          ∂PL1.ExponentialTime.timeMeasure 1 := by
      apply lintegral_mono
      intro u
      change PL1.Noise.measure (rates A) u (blockEvent s d)ᶜ ≤
        ENNReal.ofReal (errorBound s) + (Ici (s : ℝ≥0)).indicator (fun _ => 1) u
      by_cases hu : (u : ℝ) ≤ s
      · exact (noise_blockEvent_compl_le hs A hsA hd hend u hu).trans (le_add_right le_rfl)
      · have hmem : u ∈ Ici (s : ℝ≥0) := by
          exact_mod_cast (le_of_lt (lt_of_not_ge hu))
        rw [Set.indicator_of_mem hmem]
        exact (prob_le_one).trans (le_add_left le_rfl)
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_indicator measurableSet_Ici, lintegral_const,
        Measure.restrict_apply_univ, measure_univ, mul_one, one_mul, timeMeasure_unit_Ici]
      simp only [NNReal.coe_natCast]

end PL1CD.StageParameters
