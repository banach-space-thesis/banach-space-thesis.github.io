import PL1.NoiseMeasures
import PL1.CarrierAsymptotics
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Common singular carriers from coordinate averages

The coordinate random variables and noise measures below are the actual sign
product model. The general Borel–Cantelli lemma keeps the summability inputs
explicit; the subsequent moment calculations discharge the probabilistic
ingredients for the concrete coordinate averages.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal

namespace PL1.Carrier

section BorelCantelli

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The set of points belonging to all sufficiently late events. -/
def eventualSet (A : ℕ → Set Ω) : Set Ω := liminf A atTop

theorem measurableSet_eventualSet {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (eventualSet A) :=
  MeasurableSet.measurableSet_liminf hA

/-- Summable event probabilities make the eventual-event carrier null. -/
theorem measure_eventualSet_eq_zero (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : (∑' n, μ (A n)) ≠ ∞) : μ (eventualSet A) = 0 :=
  measure_liminf_atTop_eq_zero hA

/-- Summable complementary-event probabilities make the same carrier full. -/
theorem measure_eventualSet_eq_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (hcompl : (∑' n, μ (A n)ᶜ) ≠ ∞) : μ (eventualSet A) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_eventualSet hA)).mp
  filter_upwards [ae_eventually_notMem hcompl] with x hx
  change x ∈ liminf A atTop
  rw [mem_liminf_iff_eventually_mem]
  simpa only [Set.mem_compl_iff, not_not] using hx

/-- A useful one-sided Chebyshev bound for an event above a zero mean. -/
theorem measure_above_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (hmean : ∫ x, X x ∂μ = 0)
    {a : ℝ} (ha : 0 < a) :
    μ {x | a < X x} ≤ ENNReal.ofReal (variance X μ / a ^ 2) := by
  apply le_trans (measure_mono ?_) (meas_ge_le_variance_div_sq hX ha)
  intro x hx
  change a ≤ |X x - ∫ y, X y ∂μ|
  rw [hmean, sub_zero]
  exact hx.le.trans (le_abs_self _)

/-- A lower-tail Chebyshev estimate when the mean exceeds twice the threshold. -/
theorem measure_below_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) {a b : ℝ}
    (hmean : b ≤ ∫ x, X x ∂μ) (hb : 0 < b) (hab : 2 * a ≤ b) :
    μ {x | X x ≤ a} ≤ ENNReal.ofReal (variance X μ / (b / 2) ^ 2) := by
  apply le_trans (measure_mono ?_) (meas_ge_le_variance_div_sq hX (half_pos hb))
  intro x hx
  change X x ≤ a at hx
  change b / 2 ≤ |X x - ∫ y, X y ∂μ|
  have h := neg_le_abs (X x - ∫ y, X y ∂μ)
  linarith

/-- An eventual summable real upper bound suffices for finite total event mass;
the finitely many early events are finite because the ambient measure is. -/
theorem tsum_measure_ne_top_of_eventually_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (f : ℕ → ℝ) (hf : Summable f) (hf0 : ∀ n, 0 ≤ f n)
    (hA : ∀ᶠ n : ℕ in atTop, μ (A n) ≤ ENNReal.ofReal (f n)) :
    (∑' n, μ (A n)) ≠ ∞ := by
  have hreal : Summable (fun n : ℕ => (μ (A n)).toReal) := by
    apply hf.of_norm_bounded_eventually_nat
    filter_upwards [hA] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (hf0 n) hn
  have hfinite := hreal.tsum_ofReal_ne_top
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using hfinite

end BorelCantelli

open Walsh

/-- A real sign-valued coordinate random variable. -/
def coordinate (j : ℕ) (x : Walsh.Group) : ℝ := signValue (x j)

theorem continuous_coordinate (j : ℕ) : Continuous (coordinate j) := by
  change Continuous (fun x : Walsh.Group => signValue (x j))
  exact (continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply j)

theorem memLp_coordinate (μ : Measure Walsh.Group) [IsFiniteMeasure μ]
    (j : ℕ) (p : ℝ≥0∞) : MemLp (coordinate j) p μ := by
  apply MemLp.of_bound (continuous_coordinate j).aestronglyMeasurable 1
  filter_upwards [] with x
  exact (norm_signValue (x j)).le

theorem integral_coordinate_haar (j : ℕ) : ∫ x, coordinate j x ∂haar = 0 := by
  simpa only [coordinate, character_singleton] using
    integral_character_eq_zero (Finset.singleton_nonempty j)

theorem integral_coordinate_noise (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) :
    ∫ x, coordinate j x ∂Noise.measure rates u = Noise.bias rates u j := by
  simpa only [coordinate, character_singleton, Noise.rateSum, Finset.sum_singleton, Noise.bias] using
    Noise.integral_character rates u {j}

theorem variance_coordinate_le_one (μ : Measure Walsh.Group) [IsProbabilityMeasure μ]
    (j : ℕ) : variance (coordinate j) μ ≤ 1 := by
  rw [variance_eq_sub (memLp_coordinate μ j 2)]
  have hsq : coordinate j ^ (2 : ℕ) = fun _ => (1 : ℝ) := by
    funext x
    change signValue (x j) ^ 2 = 1
    rw [pow_two, signValue_mul_self]
  rw [hsq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact sub_le_self _ (sq_nonneg _)

theorem covariance_coordinate_haar {i j : ℕ} (hij : i ≠ j) :
    covariance (coordinate i) (coordinate j) haar = 0 := by
  rw [covariance_eq_sub (memLp_coordinate haar i 2) (memLp_coordinate haar j 2)]
  simp only [integral_coordinate_haar, zero_mul, sub_zero]
  simpa [coordinate, Pi.mul_apply, hij] using integral_character_mul {i} {j}

theorem covariance_coordinate_noise (rates : ℕ → ℝ≥0) (u : ℝ≥0)
    {i j : ℕ} (hij : i ≠ j) :
    covariance (coordinate i) (coordinate j) (Noise.measure rates u) = 0 := by
  have h := iIndepFun_infinitePi (P := Noise.coordinateMeasure rates u)
    (X := fun _ : ℕ => signValue) (fun _ => continuous_of_discreteTopology.measurable)
  exact (h.indepFun hij).covariance_eq_zero
    (memLp_coordinate (Noise.measure rates u) i 2)
    (memLp_coordinate (Noise.measure rates u) j 2)

/-- Pairwise uncorrelated, square-integrable summands with variance at most one
have sum variance at most their number. -/
theorem variance_sum_le_card {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (F : Finset ℕ)
    (hX : ∀ i ∈ F, MemLp (X i) 2 μ)
    (hvar : ∀ i ∈ F, variance (X i) μ ≤ 1)
    (hcov : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → covariance (X i) (X j) μ = 0) :
    variance (∑ i ∈ F, X i) μ ≤ F.card := by
  rw [variance_sum' hX]
  calc
    (∑ i ∈ F, ∑ j ∈ F, covariance (X i) (X j) μ) =
        ∑ i ∈ F, variance (X i) μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single_of_mem i hi]
      · exact covariance_self (hX i hi).aemeasurable
      · intro j hj hji
        exact hcov i hi j hj hji.symm
    _ ≤ ∑ i ∈ F, (1 : ℝ) := Finset.sum_le_sum hvar
    _ = F.card := by simp

/-- The dyadic coordinate averages, also allowing deletion of an initial segment. -/
def average (d r : ℕ) (x : Walsh.Group) : ℝ :=
  ((2 : ℝ) ^ r)⁻¹ * ∑ j ∈ Finset.range (2 ^ r), coordinate (d + j) x

theorem continuous_average (d r : ℕ) : Continuous (average d r) := by
  unfold average
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j hj
  exact continuous_coordinate _

theorem memLp_average (μ : Measure Walsh.Group) [IsFiniteMeasure μ] (d r : ℕ) :
    MemLp (average d r) 2 μ := by
  apply (memLp_finsetSum (Finset.range (2 ^ r))
    (fun j _ => memLp_coordinate μ (d + j) 2)).const_mul

theorem integral_average_haar (d r : ℕ) : ∫ x, average d r x ∂haar = 0 := by
  unfold average
  rw [integral_const_mul, integral_finsetSum]
  · simp only [integral_coordinate_haar, Finset.sum_const_zero, mul_zero]
  · intro j hj
    exact (memLp_coordinate haar (d + j) 2).integrable (by norm_num)

theorem integral_average_noise (rates : ℕ → ℝ≥0) (u : ℝ≥0) (d r : ℕ) :
    ∫ x, average d r x ∂Noise.measure rates u =
      ((2 : ℝ) ^ r)⁻¹ * ∑ j ∈ Finset.range (2 ^ r), Noise.bias rates u (d + j) := by
  unfold average
  rw [integral_const_mul, integral_finsetSum]
  · simp only [integral_coordinate_noise]
  · intro j hj
    exact (memLp_coordinate (Noise.measure rates u) (d + j) 2).integrable (by norm_num)

theorem variance_average_le (μ : Measure Walsh.Group) [IsProbabilityMeasure μ] (d r : ℕ)
    (hcov : ∀ i j : ℕ, i ≠ j → covariance (coordinate i) (coordinate j) μ = 0) :
    variance (average d r) μ ≤ (1 / 2 : ℝ) ^ r := by
  have hsum := variance_sum_le_card μ (fun j => coordinate (d + j)) (Finset.range (2 ^ r))
    (fun j _ => memLp_coordinate μ (d + j) 2)
    (fun j _ => variance_coordinate_le_one μ (d + j))
    (fun i _ j _ hij => hcov _ _ (by omega))
  simp only [Finset.card_range, Nat.cast_pow, Nat.cast_ofNat] at hsum
  have havg : average d r =
      ((2 : ℝ) ^ r)⁻¹ • ∑ j ∈ Finset.range (2 ^ r), coordinate (d + j) := by
    funext x
    simp only [average, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [havg, variance_smul]
  calc
    (((2 : ℝ) ^ r)⁻¹) ^ 2 *
        variance (∑ j ∈ Finset.range (2 ^ r), coordinate (d + j)) μ
        ≤ (((2 : ℝ) ^ r)⁻¹) ^ 2 * (2 : ℝ) ^ r :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (1 / 2 : ℝ) ^ r := by
      have hne : (2 : ℝ) ^ r ≠ 0 := by positivity
      rw [one_div_pow, sq]
      field_simp

theorem variance_average_haar_le (d r : ℕ) :
    variance (average d r) haar ≤ (1 / 2 : ℝ) ^ r :=
  variance_average_le haar d r (fun _ _ hij => covariance_coordinate_haar hij)

theorem variance_average_noise_le (rates : ℕ → ℝ≥0) (u : ℝ≥0) (d r : ℕ) :
    variance (average d r) (Noise.measure rates u) ≤ (1 / 2 : ℝ) ^ r :=
  variance_average_le (Noise.measure rates u) d r
    (fun _ _ hij => covariance_coordinate_noise rates u hij)

open CarrierAsymptotics

/-- The open coordinate-average events defining the common carrier. -/
def highEvent (d r : ℕ) : Set Walsh.Group := {x | threshold r < average d r x}

/-- One Borel set for each deleted finite prefix, independent of noise time. -/
def commonSet (d : ℕ) : Set Walsh.Group := eventualSet (highEvent d)

theorem measurableSet_highEvent (d r : ℕ) : MeasurableSet (highEvent d r) :=
  measurableSet_lt measurable_const (continuous_average d r).measurable

theorem measurableSet_commonSet (d : ℕ) : MeasurableSet (commonSet d) :=
  measurableSet_eventualSet (measurableSet_highEvent d)

theorem haar_highEvent_le (d r : ℕ) :
    haar (highEvent d r) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ r / (threshold r) ^ 2) := by
  apply (measure_above_le haar (average d r) (memLp_average haar d r)
    (integral_average_haar d r) (threshold_pos r)).trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right (variance_average_haar_le d r) (sq_nonneg _)

/-- The same carrier is Haar-null after deleting any finite number of coordinates. -/
theorem haar_commonSet_eq_zero (d : ℕ) : haar (commonSet d) = 0 := by
  apply measure_eventualSet_eq_zero
  exact ne_top_of_le_ne_top summable_haar_failure_bound.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum (haar_highEvent_le d))

theorem bias_schurRates_ge (u : ℝ≥0) (d r j : ℕ) (hj : j < 2 ^ r) :
    biasLower u ((d : ℝ) + 1) r ≤ Noise.bias Noise.schurRates u (d + j) := by
  apply Real.exp_le_exp.mpr
  change -(u : ℝ) * Real.sqrt (((r : ℝ) + ((d : ℝ) + 1)) * Real.log 2) ≤
    -(u : ℝ) * Real.sqrt (Real.log ((d + j : ℕ) + 2 : ℝ))
  have h := mul_le_mul_of_nonpos_left (shifted_rate_le d r j hj)
    (neg_nonpos.mpr u.coe_nonneg)
  simpa only [add_assoc] using h

theorem integral_average_schurRates_ge (u : ℝ≥0) (d r : ℕ) :
    biasLower u ((d : ℝ) + 1) r ≤ ∫ x, average d r x ∂Noise.measure Noise.schurRates u := by
  rw [integral_average_noise]
  have hsum : (2 : ℝ) ^ r * biasLower u ((d : ℝ) + 1) r ≤
      ∑ j ∈ Finset.range (2 ^ r), Noise.bias Noise.schurRates u (d + j) := by
    calc
      _ = ∑ _j ∈ Finset.range (2 ^ r), biasLower u ((d : ℝ) + 1) r := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj =>
        bias_schurRates_ge u d r j (Finset.mem_range.mp hj))
  have hp : (2 : ℝ) ^ r ≠ 0 := by positivity
  calc
    biasLower u ((d : ℝ) + 1) r =
        ((2 : ℝ) ^ r)⁻¹ * ((2 : ℝ) ^ r * biasLower u ((d : ℝ) + 1) r) := by
      rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem eventually_noise_highEvent_compl_le (u : ℝ≥0) (d : ℕ) :
    ∀ᶠ r : ℕ in atTop, Noise.measure Noise.schurRates u (highEvent d r)ᶜ ≤
      ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ r *
        Real.exp (2 * (u : ℝ) * Real.sqrt (((r : ℝ) + ((d : ℝ) + 1)) * Real.log 2))) := by
  filter_upwards [eventually_two_threshold_le_biasLower u u.coe_nonneg
    ((d : ℝ) + 1) (by positivity)] with r hr
  have heq : (highEvent d r)ᶜ = {x | average d r x ≤ threshold r} := by
    ext x
    simp only [highEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  rw [heq]
  apply (measure_below_le (Noise.measure Noise.schurRates u) (average d r)
    (memLp_average (Noise.measure Noise.schurRates u) d r)
    (integral_average_schurRates_ge u d r) (biasLower_pos _ _ _) hr).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (1 / 2 : ℝ) ^ r / (biasLower u ((d : ℝ) + 1) r / 2) ^ 2 :=
      div_le_div_of_nonneg_right (variance_average_noise_le Noise.schurRates u d r)
        (sq_nonneg _)
    _ = _ := noise_failure_bound_eq u ((d : ℝ) + 1) r

/-- The concrete common Borel carrier carries every product noise measure for
the Schur rates, including time zero, after any deleted finite prefix. -/
theorem noise_commonSet_eq_one (u : ℝ≥0) (d : ℕ) :
    Noise.measure Noise.schurRates u (commonSet d) = 1 := by
  apply measure_eventualSet_eq_one _ _ (measurableSet_highEvent d)
  apply tsum_measure_ne_top_of_eventually_le _ _
    (fun r : ℕ => 4 * (1 / 2 : ℝ) ^ r *
      Real.exp (2 * (u : ℝ) * Real.sqrt (((r : ℝ) + ((d : ℝ) + 1)) * Real.log 2)))
    (summable_noise_failure_bound u u.coe_nonneg ((d : ℝ) + 1) (by positivity))
  · intro r
    positivity
  · exact eventually_noise_highEvent_compl_le u d

/-- The carrier genuinely depends only on the coordinates remaining after the
deleted prefix. -/
theorem mem_commonSet_iff_of_tail_eq (d : ℕ) {x y : Walsh.Group}
    (hxy : ∀ j : ℕ, x (d + j) = y (d + j)) :
    x ∈ commonSet d ↔ y ∈ commonSet d := by
  have havg (r : ℕ) : average d r x = average d r y := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg signValue (hxy j)
  simp only [commonSet, eventualSet, mem_liminf_iff_eventually_mem,
    highEvent, Set.mem_ofPred_eq, havg]

theorem integral_average_constantRates (u : ℝ≥0) (d r : ℕ) :
    ∫ x, average d r x ∂Noise.measure Noise.constantRates u = Real.exp (-(u : ℝ)) := by
  rw [integral_average_noise]
  simp only [Noise.bias, Noise.constantRates, NNReal.coe_one, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ r ≠ 0), one_mul]

theorem threshold_tendsto_zero : Tendsto threshold atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
  apply Real.exp_lt_one_iff.mpr
  linarith [log_two_pos]

/-- The same concrete carrier also carries every constant-rate product law. -/
theorem noise_constantRates_commonSet_eq_one (u : ℝ≥0) (d : ℕ) :
    Noise.measure Noise.constantRates u (commonSet d) = 1 := by
  have hpos : 0 < Real.exp (-(u : ℝ)) := Real.exp_pos _
  have hthreshold : ∀ᶠ r : ℕ in atTop, 2 * threshold r ≤ Real.exp (-(u : ℝ)) := by
    filter_upwards [threshold_tendsto_zero.eventually_lt_const (half_pos hpos)] with r hr
    linarith
  have hgeom : Summable (fun r : ℕ => (1 / 2 : ℝ) ^ r) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply measure_eventualSet_eq_one _ _ (measurableSet_highEvent d)
  apply tsum_measure_ne_top_of_eventually_le _ _
    (fun r : ℕ => (1 / 2 : ℝ) ^ r / (Real.exp (-(u : ℝ)) / 2) ^ 2)
    (hgeom.div_const _)
  · intro r
    positivity
  · filter_upwards [hthreshold] with r hr
    have heq : (highEvent d r)ᶜ = {x | average d r x ≤ threshold r} := by
      ext x
      simp only [highEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [heq]
    apply (measure_below_le (Noise.measure Noise.constantRates u) (average d r)
      (memLp_average (Noise.measure Noise.constantRates u) d r)
      (integral_average_constantRates u d r).ge hpos hr).trans
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (variance_average_noise_le Noise.constantRates u d r)
      (sq_nonneg _)

/-- Lemma 3.1 for the actual Schur-rate product probabilities, with one Borel
Haar-null set independent of time and with arbitrary finite-prefix deletion. -/
theorem exists_common_haar_null_carrier (d : ℕ) :
    ∃ N : Set Walsh.Group, MeasurableSet N ∧ haar N = 0 ∧
      ∀ u : ℝ≥0, Noise.measure Noise.schurRates u N = 1 :=
  ⟨commonSet d, measurableSet_commonSet d, haar_commonSet_eq_zero d,
    fun u => noise_commonSet_eq_one u d⟩

/-- A single tail-dependent Borel Haar-null set works for both rate choices in
the paper, uniformly over every nonnegative time. -/
theorem exists_common_haar_null_carrier_both_rates (d : ℕ) :
    ∃ N : Set Walsh.Group, MeasurableSet N ∧ haar N = 0 ∧
      (∀ x y : Walsh.Group, (∀ j : ℕ, x (d + j) = y (d + j)) → (x ∈ N ↔ y ∈ N)) ∧
      (∀ u : ℝ≥0, Noise.measure Noise.schurRates u N = 1) ∧
      ∀ u : ℝ≥0, Noise.measure Noise.constantRates u N = 1 :=
  ⟨commonSet d, measurableSet_commonSet d, haar_commonSet_eq_zero d,
    fun _ _ h => mem_commonSet_iff_of_tail_eq d h,
    fun u => noise_commonSet_eq_one u d, fun u => noise_constantRates_commonSet_eq_one u d⟩

end PL1.Carrier
