import PL1.IntrinsicTailNorm

/-!
# The constant one is exposed in the actual intrinsic unit ball

The exposing functional is the Haar integral of the zeroth coordinate.
Positive rates force every resolvent-fixed L1 function to be constant; this
is proved by strong convergence of resolvent iterates on the dense Walsh span.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PL1.IntrinsicExposedPoint
open Walsh WalshExpectations Noise IntrinsicGraph IntrinsicTailNorm

variable (K : Type*) [RCLike K]

def meanL1 : Lp K 1 haar →L[K] K := L1.integralCLM' K

theorem meanL1_apply (f : Lp K 1 haar) : meanL1 K f = ∫ x, f x ∂haar := by
  rw [meanL1, ← L1.integral_eq']
  exact L1.integral_eq_integral f

theorem norm_meanL1_apply_le (f : Lp K 1 haar) : ‖meanL1 K f‖ ≤ ‖f‖ := by
  rw [meanL1, ← L1.integral_eq']
  exact L1.norm_integral_le f

theorem meanL1_character (F : Finset ℕ) :
    meanL1 K (scalarCharacterLp K 1 F) = if F = ∅ then 1 else 0 := by
  rw [meanL1_apply, integral_congr_ae (coeFn_scalarCharacterLp K 1 F)]
  simp only [scalarCharacter, integral_ofReal, Walsh.integral_character]
  split_ifs <;> simp

theorem expectation_zero_eq_mean :
    expectationL1 K 0 = (meanL1 K).smulRight (scalarCharacterLp K 1 ∅) := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [expectationL1_character, Finset.range_zero, Finset.subset_empty,
    ContinuousLinearMap.smulRight_apply, meanL1_character]
  split_ifs with h
  · subst F; simp
  · simp

def resolventIterate (rates : ℕ → ℝ≥0) (t : PositiveTime) :
    ℕ → Lp K 1 haar →L[K] Lp K 1 haar
  | 0 => ContinuousLinearMap.id K _
  | n + 1 => (resolventL1 K rates t).comp (resolventIterate rates t n)

theorem norm_resolventIterate_le (rates : ℕ → ℝ≥0) (t : PositiveTime) (n : ℕ) :
    ‖resolventIterate K rates t n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (norm_resolventL1_le_one K rates t)
        (norm_nonneg _)).trans (by simpa only [one_mul] using ih))

theorem resolventIterate_character (rates : ℕ → ℝ≥0) (t : PositiveTime)
    (n : ℕ) (F : Finset ℕ) :
    resolventIterate K rates t n (scalarCharacterLp K 1 F) =
      ((((1 + (t : ℝ) * rateSum rates F)⁻¹) ^ n : ℝ) : K) • scalarCharacterLp K 1 F := by
  induction n with
  | zero => simp only [resolventIterate, ContinuousLinearMap.id_apply, pow_zero,
      RCLike.ofReal_one, one_smul]
  | succ n ih =>
    rw [resolventIterate, ContinuousLinearMap.comp_apply, ih, map_smul,
      resolventL1_scalarCharacter, smul_smul, ← RCLike.ofReal_mul, pow_succ]

theorem rateSum_pos {rates : ℕ → ℝ≥0} (hrates : ∀ j, 0 < rates j)
    {F : Finset ℕ} (hF : F.Nonempty) : 0 < rateSum rates F := by
  unfold rateSum
  exact Finset.sum_pos (fun j _ => hrates j) hF

theorem tendsto_resolventIterate (rates : ℕ → ℝ≥0) (hrates : ∀ j, 0 < rates j)
    (t : PositiveTime) (f : Lp K 1 haar) :
    Tendsto (fun n => resolventIterate K rates t n f) atTop (𝓝 (expectationL1 K 0 f)) := by
  apply tendsto_apply_of_dense_span (scalarCharacterLp K 1)
    (dense_span_scalarCharacterLp K 1 (by norm_num)) (resolventIterate K rates t)
    (expectationL1 K 0) atTop 1 (norm_resolventIterate_le K rates t)
  intro F
  by_cases hF : F = ∅
  · subst F
    simpa only [resolventIterate_character, rateSum, Finset.sum_empty, mul_zero,
      add_zero, inv_one, one_pow, RCLike.ofReal_one, one_smul,
      expectationL1_character, Finset.empty_subset, ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => scalarCharacterLp K 1 ∅)
        atTop (𝓝 (scalarCharacterLp K 1 ∅)))
  · have hr : 0 < rateSum rates F := rateSum_pos hrates (Finset.nonempty_iff_ne_empty.mpr hF)
    have htr : 0 < (t : ℝ) * rateSum rates F := mul_pos t.property hr
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr (by positivity : 0 ≤ 1 + (t : ℝ) * rateSum rates F))
      (by apply (inv_lt_one₀ (by positivity : 0 < 1 + (t : ℝ) * rateSum rates F)).mpr
          nlinarith [mul_pos t.property hr])
    have hc := ((RCLike.continuous_ofReal (K := K)).tendsto 0).comp hp
    convert hc.smul_const (scalarCharacterLp K 1 F) using 1
    · funext n
      rw [resolventIterate_character]
      rfl
    · simp only [expectationL1_character, Finset.range_zero, Finset.subset_empty,
        hF, ite_false, RCLike.ofReal_zero, zero_smul]

theorem eq_mean_smul_of_resolvent_fixed (rates : ℕ → ℝ≥0)
    (hrates : ∀ j, 0 < rates j) (t : PositiveTime) (f : Lp K 1 haar)
    (hf : resolventL1 K rates t f = f) :
    f = meanL1 K f • scalarCharacterLp K 1 ∅ := by
  have hiter (n : ℕ) : resolventIterate K rates t n f = f := by
    induction n with
    | zero => rfl
    | succ n ih => rw [resolventIterate, ContinuousLinearMap.comp_apply, ih, hf]
  have h := tendsto_resolventIterate K rates hrates t f
  simp only [hiter] at h
  have he := tendsto_nhds_unique tendsto_const_nhds h
  rwa [expectation_zero_eq_mean, ContinuousLinearMap.smulRight_apply] at he

def integralFunctional (rates : ℕ → ℝ≥0) :
    (dyadicSystem K rates).IntrinsicSpace →L[K] K :=
  (meanL1 K).comp (evalZero (dyadicSystem K rates).analysis)

theorem integralFunctional_apply (rates : ℕ → ℝ≥0)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    integralFunctional K rates x = ∫ s, evalZero (dyadicSystem K rates).analysis x s ∂haar :=
  meanL1_apply K _

theorem integralFunctional_constant (rates : ℕ → ℝ≥0) :
    integralFunctional K rates (intrinsicCharacter K rates ∅) = 1 := by
  simp only [integralFunctional, ContinuousLinearMap.comp_apply,
    evalZero_intrinsicCharacter, meanL1_character, ite_true]

theorem norm_integralFunctional_apply_le (rates : ℕ → ℝ≥0)
    (x : (dyadicSystem K rates).IntrinsicSpace) :
    ‖integralFunctional K rates x‖ ≤ ‖x‖ :=
  (norm_meanL1_apply_le K _).trans (norm_evalZero_le _ x)

theorem norm_integralFunctional (rates : ℕ → ℝ≥0) : ‖integralFunctional K rates‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using norm_integralFunctional_apply_le K rates x
  · have h := (integralFunctional K rates).le_opNorm (intrinsicCharacter K rates ∅)
    simpa only [integralFunctional_constant, norm_one, norm_intrinsicConstant, mul_one] using h

theorem eq_one_of_norm_le_one_re_eq_one {z : K} (hz : ‖z‖ ≤ 1) (hre : RCLike.re z = 1) :
    z = 1 := by
  have hnorm : ‖z‖ = 1 := le_antisymm hz (by simpa only [hre] using RCLike.re_le_norm z)
  have he := RCLike.norm_le_re_iff_eq_norm.mp (hz.trans_eq hre.symm)
  simpa only [hnorm, RCLike.ofReal_one] using he

/-- Equality in the integral bound leaves no positive-index intrinsic norm
mass. One nonzero coordinate weight therefore makes the resolvent fix the
underlying L1 function. -/
theorem resolvent_fixed_of_integral_maximum (rates : ℕ → ℝ≥0)
    (x : (dyadicSystem K rates).IntrinsicSpace) (hx : ‖x‖ ≤ 1)
    (hφx : RCLike.re (integralFunctional K rates x) = 1) :
    resolventL1 K rates (dyadicTime 1) (evalZero (dyadicSystem K rates).analysis x) =
      evalZero (dyadicSystem K rates).analysis x := by
  have hbase : 1 ≤ ‖evalZero (dyadicSystem K rates).analysis x‖ := by
    have h := (RCLike.re_le_norm (integralFunctional K rates x)).trans (norm_meanL1_apply_le K _)
    rwa [hφx] at h
  have hsum := (IntrinsicSpikeEstimates.summable_norm_coord x).sum_le_tsum
    ({0, 1} : Finset ℕ) (fun _ _ => norm_nonneg _)
  rw [← norm_eq_tsum] at hsum
  simp only [Finset.sum_pair (by norm_num : (0:ℕ) ≠ 1)] at hsum
  have hz : coord (dyadicSystem K rates).analysis 1 x = 0 := by
    apply norm_eq_zero.mp
    change ‖evalZero (dyadicSystem K rates).analysis x‖ +
      ‖coord (dyadicSystem K rates).analysis 1 x‖ ≤ ‖x‖ at hsum
    linarith [norm_nonneg (coord (dyadicSystem K rates).analysis 1 x)]
  rw [coord_eq] at hz
  change (((ResolventEstimates.dyadicRatio ^ 1)⁻¹ : ℝ) : K) •
    (evalZero (dyadicSystem K rates).analysis x -
      resolventL1 K rates (dyadicTime 1) (evalZero (dyadicSystem K rates).analysis x)) = 0 at hz
  have hcoef : (((ResolventEstimates.dyadicRatio ^ 1)⁻¹ : ℝ) : K) ≠ 0 := by
    exact_mod_cast inv_ne_zero (pow_ne_zero _ ResolventEstimates.dyadicRatio_pos.ne')
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hcoef)).symm

/-- The Haar integral exposes exactly the constant one in the original
intrinsic unit ball whenever every rate is strictly positive. -/
theorem integralFunctional_exposes_constant (rates : ℕ → ℝ≥0)
    (hrates : ∀ j, 0 < rates j)
    (x : (dyadicSystem K rates).IntrinsicSpace) (hx : ‖x‖ ≤ 1)
    (hφx : RCLike.re (integralFunctional K rates x) = 1) :
    x = intrinsicCharacter K rates ∅ := by
  have hfixed := resolvent_fixed_of_integral_maximum K rates x hx hφx
  have hmean := eq_mean_smul_of_resolvent_fixed K rates hrates (dyadicTime 1) _ hfixed
  have hone := eq_one_of_norm_le_one_re_eq_one K
    ((norm_integralFunctional_apply_le K rates x).trans hx) hφx
  apply evalZero_injective (dyadicSystem K rates).analysis
  rw [evalZero_intrinsicCharacter]
  change meanL1 K (evalZero (dyadicSystem K rates).analysis x) = 1 at hone
  simpa only [hone, one_smul] using hmean

theorem schurRates_strictlyPositive (j : ℕ) : 0 < schurRates j := by
  change (0 : ℝ) < Real.sqrt (Real.log (j + 2))
  apply Real.sqrt_pos.mpr
  apply Real.log_pos
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem integralFunctional_maximum_iff (rates : ℕ → ℝ≥0)
    (hrates : ∀ j, 0 < rates j) (x : (dyadicSystem K rates).IntrinsicSpace)
    (hx : ‖x‖ ≤ 1) :
    RCLike.re (integralFunctional K rates x) = 1 ↔ x = intrinsicCharacter K rates ∅ := by
  constructor
  · exact integralFunctional_exposes_constant K rates hrates x hx
  · intro he
    rw [he, integralFunctional_constant, RCLike.one_re]

theorem integralFunctional_strict_maximum (rates : ℕ → ℝ≥0)
    (hrates : ∀ j, 0 < rates j) (x : (dyadicSystem K rates).IntrinsicSpace)
    (hx : ‖x‖ ≤ 1) (hxc : x ≠ intrinsicCharacter K rates ∅) :
    RCLike.re (integralFunctional K rates x) < 1 := by
  apply lt_of_le_of_ne
    ((RCLike.re_le_norm _).trans ((norm_integralFunctional_apply_le K rates x).trans hx))
  intro h
  exact hxc (integralFunctional_exposes_constant K rates hrates x hx h)

theorem schur_integralFunctional_exposes_constant
    (x : (dyadicSystem K schurRates).IntrinsicSpace) (hx : ‖x‖ ≤ 1)
    (hφx : RCLike.re (integralFunctional K schurRates x) = 1) :
    x = intrinsicCharacter K schurRates ∅ :=
  integralFunctional_exposes_constant K schurRates schurRates_strictlyPositive x hx hφx

theorem constant_integralFunctional_exposes_constant
    (x : (dyadicSystem K constantRates).IntrinsicSpace) (hx : ‖x‖ ≤ 1)
    (hφx : RCLike.re (integralFunctional K constantRates x) = 1) :
    x = intrinsicCharacter K constantRates ∅ :=
  integralFunctional_exposes_constant K constantRates (fun _ => zero_lt_one) x hx hφx

end PL1.IntrinsicExposedPoint
