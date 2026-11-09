import PL1CD.StageAsymptotics
import PL1.SingularCarrier

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace PL1CD.StageParameters

def blockAverage (d k : ℕ) (x : PL1.Walsh.Group) : ℝ :=
  (k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, PL1.Carrier.coordinate (d + j) x

theorem continuous_blockAverage (d k : ℕ) : Continuous (blockAverage d k) := by
  unfold blockAverage
  exact continuous_const.mul (continuous_finsetSum _
    (fun j _ => PL1.Carrier.continuous_coordinate _))

theorem memLp_blockAverage (μ : Measure PL1.Walsh.Group) [IsFiniteMeasure μ] (d k : ℕ) :
    MemLp (blockAverage d k) 2 μ :=
  (memLp_finsetSum (Finset.range k) (fun j _ => PL1.Carrier.memLp_coordinate μ (d + j) 2)).const_mul _

theorem integral_blockAverage_haar (d k : ℕ) :
    ∫ x, blockAverage d k x ∂PL1.Walsh.haar = 0 := by
  unfold blockAverage
  rw [integral_const_mul, integral_finsetSum]
  · simp [PL1.Carrier.integral_coordinate_haar]
  · intro j _
    exact (PL1.Carrier.memLp_coordinate PL1.Walsh.haar (d + j) 2).integrable (by norm_num)

theorem variance_blockAverage_le (μ : Measure PL1.Walsh.Group) [IsProbabilityMeasure μ]
    (d k : ℕ) (hcov : ∀ i j : ℕ, i ≠ j →
      covariance (PL1.Carrier.coordinate i) (PL1.Carrier.coordinate j) μ = 0) :
    variance (blockAverage d k) μ ≤ (k : ℝ)⁻¹ := by
  have hsum := PL1.Carrier.variance_sum_le_card μ
    (fun j => PL1.Carrier.coordinate (d + j)) (Finset.range k)
    (fun j _ => PL1.Carrier.memLp_coordinate μ (d + j) 2)
    (fun j _ => PL1.Carrier.variance_coordinate_le_one μ (d + j))
    (fun i _ j _ hij => hcov _ _ (by omega))
  simp only [Finset.card_range] at hsum
  have heq : blockAverage d k =
      (k : ℝ)⁻¹ • ∑ j ∈ Finset.range k, PL1.Carrier.coordinate (d + j) := by
    funext x
    simp [blockAverage, Finset.sum_apply]
  rw [heq, variance_smul]
  calc
    _ ≤ ((k : ℝ)⁻¹) ^ 2 * k := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (k : ℝ)⁻¹ := by
      by_cases hk : k = 0
      · simp [hk]
      · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        field_simp

def threshold (s : ℕ) : ℝ := Real.exp (-(s : ℝ) * (low s : ℝ))

def errorBound (s : ℕ) : ℝ := (16 * (s : ℝ) ^ 2)⁻¹

def stageEvent (s : ℕ) : Set PL1.Walsh.Group :=
  {x | threshold s / 2 < blockAverage (dimension (s - 1)) (blockSize s) x}

theorem measurableSet_stageEvent (s : ℕ) : MeasurableSet (stageEvent s) :=
  measurableSet_lt measurable_const (continuous_blockAverage _ _).measurable

theorem chebyshev_ratio_le {s : ℕ} (hs : 0 < s) :
    4 / ((blockSize s : ℝ) * threshold s ^ 2) ≤ errorBound s := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hk : (0 : ℝ) < blockSize s := by exact_mod_cast blockSize_pos hs
  have hq : 0 < threshold s := Real.exp_pos _
  have hexp : Real.exp (2 * (s : ℝ) * (low s : ℝ)) * threshold s ^ 2 = 1 := by
    unfold threshold
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right (blockSize_lower s) (sq_nonneg (threshold s))
  simp only [mul_assoc] at hexp
  have hlower : 64 * (s : ℝ) ^ 2 ≤ (blockSize s : ℝ) * threshold s ^ 2 := by
    simpa only [mul_assoc, hexp, mul_one] using h
  unfold errorBound
  rw [← one_div]
  apply (div_le_div_iff₀ (mul_pos hk (sq_pos_of_pos hq)) (by positivity)).mpr
  nlinarith

theorem haar_stageEvent_le {s : ℕ} (hs : 0 < s) :
    PL1.Walsh.haar (stageEvent s) ≤ ENNReal.ofReal (errorBound s) := by
  have hvar := variance_blockAverage_le PL1.Walsh.haar (dimension (s - 1)) (blockSize s)
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

theorem rates_on_first_block {s : ℕ} (hs : 0 < s) (A : Set ℕ) (hsA : s ∈ A)
    {j : ℕ} (hj : j < blockSize s) :
    rates A (dimension (s - 1) + j) = (low s : ℝ≥0) := by
  have hrec : dimension s = dimension (s - 1) + repetitions s * blockSize s := by
    simpa [Nat.sub_add_cancel hs] using dimension_succ (s - 1)
  have hr : 1 ≤ repetitions s := repetitions_pos hs
  have hk := Nat.mul_le_mul_right (blockSize s) hr
  have heq := coordinateStage_of_stage hs
    (show dimension (s - 1) ≤ dimension (s - 1) + j by omega)
    (show dimension (s - 1) + j < dimension s by omega)
  simp [rates, heq, stageRate, hsA]

theorem integral_blockAverage_noise_ge {s : ℕ} (hs : 0 < s)
    (A : Set ℕ) (hsA : s ∈ A) (u : ℝ≥0) (hu : (u : ℝ) ≤ s) :
    threshold s ≤ ∫ x, blockAverage (dimension (s - 1)) (blockSize s) x
      ∂PL1.Noise.measure (rates A) u := by
  have hk : (0 : ℝ) < blockSize s := by exact_mod_cast blockSize_pos hs
  unfold blockAverage
  rw [integral_const_mul, integral_finsetSum]
  · calc
      _ ≥ (blockSize s : ℝ)⁻¹ * ∑ _j ∈ Finset.range (blockSize s), threshold s := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
        apply Finset.sum_le_sum
        intro j hj
        rw [PL1.Carrier.integral_coordinate_noise, PL1.Noise.bias,
          rates_on_first_block hs A hsA (Finset.mem_range.mp hj)]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg hu) (by positivity)
      _ = threshold s := by simp [hk.ne']
  · intro j _
    exact (PL1.Carrier.memLp_coordinate (PL1.Noise.measure (rates A) u) _ 2).integrable (by norm_num)

theorem noise_stageEvent_compl_le {s : ℕ} (hs : 0 < s)
    (A : Set ℕ) (hsA : s ∈ A) (u : ℝ≥0) (hu : (u : ℝ) ≤ s) :
    PL1.Noise.measure (rates A) u (stageEvent s)ᶜ ≤ ENNReal.ofReal (errorBound s) := by
  have hvar := variance_blockAverage_le (PL1.Noise.measure (rates A) u)
    (dimension (s - 1)) (blockSize s)
    (fun i j hij => PL1.Carrier.covariance_coordinate_noise (rates A) u hij)
  have hsubset : (stageEvent s)ᶜ =
      {x | blockAverage (dimension (s - 1)) (blockSize s) x ≤ threshold s / 2} := by
    ext x
    simp [stageEvent]
  rw [hsubset]
  apply (PL1.Carrier.measure_below_le (PL1.Noise.measure (rates A) u) _
    (memLp_blockAverage _ _ _) (integral_blockAverage_noise_ge hs A hsA u hu)
    (Real.exp_pos _) (by linarith : 2 * (threshold s / 2) ≤ threshold s)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (blockSize s : ℝ)⁻¹ / (threshold s / 2) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 4 / ((blockSize s : ℝ) * threshold s ^ 2) := by ring
    _ ≤ errorBound s := chebyshev_ratio_le hs

end PL1CD.StageParameters
