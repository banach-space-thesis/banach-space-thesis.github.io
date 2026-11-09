import PL1.NoiseSemigroup
import PL1.LpInclusions
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import PL1.BonamiHaarBridge
import PL1.ConvolutionHypercontractivity

/-! # Dense extension of finite Walsh noise estimates to actual Haar Lp

The norm hypothesis is explicit in the extension lemmas. The finite-cube
Bonami theorem supplies it in the final application.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PL1.NoiseHypercontractivity
open Walsh Noise

variable (K : Type*) [RCLike K]

abbrev Coefficients := Finset ℕ →₀ K

def polynomialLp (p : ℝ≥0∞) [Fact (1 ≤ p)] : Coefficients K →ₗ[K] Lp K p haar :=
  Finsupp.linearCombination K (scalarCharacterLp K p)

def noisePolynomial (u : ℝ≥0) : Coefficients K →ₗ[K] Lp K 2 haar :=
  Finsupp.linearCombination K (fun F =>
    ((Real.exp (-(u : ℝ) * F.card) : ℝ) : K) • scalarCharacterLp K 2 F)

@[simp] theorem polynomialLp_single (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : Finset ℕ) (a : K) :
    polynomialLp K p (Finsupp.single F a) = a • scalarCharacterLp K p F := by
  simp [polynomialLp]

@[simp] theorem noisePolynomial_single (u : ℝ≥0) (F : Finset ℕ) (a : K) :
    noisePolynomial K u (Finsupp.single F a) =
      a • (((Real.exp (-(u : ℝ) * F.card) : ℝ) : K) • scalarCharacterLp K 2 F) := by
  simp [noisePolynomial]

theorem polynomialLp_denseRange (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (polynomialLp K p) := by
  change Dense (Set.range (polynomialLp K p))
  rw [← LinearMap.coe_range, polynomialLp, Finsupp.range_linearCombination]
  exact dense_span_scalarCharacterLp K p hp

theorem inclusion_polynomialLp (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (c : Coefficients K) :
    ProbabilityLp.inclusion haar p q hpq (polynomialLp K q c) = polynomialLp K p c := by
  have h : (ProbabilityLp.inclusion (𝕜 := K) haar p q hpq).toLinearMap.comp
      (polynomialLp K q) = polynomialLp K p := by
    apply Finsupp.lhom_ext
    intro F a
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, polynomialLp_single,
      map_smul]
    congr 1
    exact ProbabilityLp.inclusion_toLp haar p q hpq (memLp_scalarCharacter K q F)
  exact LinearMap.congr_fun h c

theorem noisePolynomial_overlap (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : ℝ≥0)
    (c : Coefficients K) :
    l2ToL1 (noisePolynomial K u c) = noiseL1 K constantRates u
      (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) (polynomialLp K p c)) := by
  rw [inclusion_polynomialLp]
  have h : l2ToL1.toLinearMap.comp (noisePolynomial K u) =
      (noiseL1 K constantRates u).toLinearMap.comp (polynomialLp K 1) := by
    apply Finsupp.lhom_ext
    intro F a
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, noisePolynomial_single,
      polynomialLp_single, map_smul, noiseL1_character, l2ToL1_scalarCharacter]
    simp [rateSum, constantRates]
  exact LinearMap.congr_fun h c

def PolynomialBound (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : ℝ≥0) : Prop :=
  ∀ c : Coefficients K, ‖noisePolynomial K u c‖ ≤ ‖polynomialLp K p c‖

/-- Completion of the finite Walsh map. Its bound and noise identity are
proved below whenever the explicitly stated polynomial estimate holds. -/
def polynomialExtension (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : ℝ≥0) :
    Lp K p haar →L[K] Lp K 2 haar :=
  (noisePolynomial K u).extendOfNorm (polynomialLp K p)

theorem polynomialExtension_polynomial (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : ℝ≥0) (hbound : PolynomialBound K p u) (c : Coefficients K) :
    polynomialExtension K p u (polynomialLp K p c) = noisePolynomial K u c :=
  LinearMap.extendOfNorm_eq (polynomialLp_denseRange K p hp)
    ⟨1, fun c => by simpa only [one_mul] using hbound c⟩ c

theorem norm_polynomialExtension_le_one (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : ℝ≥0) (hbound : PolynomialBound K p u) :
    ‖polynomialExtension K p u‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le (polynomialLp_denseRange K p hp) zero_le_one
    (fun c => by simpa only [one_mul] using hbound c)

theorem polynomialExtension_overlap (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : ℝ≥0) (hbound : PolynomialBound K p u) (f : Lp K p haar) :
    l2ToL1 (polynomialExtension K p u f) =
      noiseL1 K constantRates u (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f) := by
  have h : l2ToL1.comp (polynomialExtension K p u) =
      (noiseL1 K constantRates u).comp
        (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p)) := by
    apply ContinuousLinearMap.ext_on (dense_span_scalarCharacterLp K p hp)
    rintro x ⟨F, rfl⟩
    have he := polynomialExtension_polynomial K p hp u hbound (Finsupp.single F 1)
    have ho := noisePolynomial_overlap K p u (Finsupp.single F 1)
    simp only [polynomialLp_single, one_smul] at he ho
    simpa only [ContinuousLinearMap.comp_apply, he] using ho
  exact congrArg (fun T : Lp K p haar →L[K] Lp K 1 haar => T f) h

theorem coeFn_weighted_polynomial (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Finset ℕ → K) (c : Coefficients K) :
    (Finsupp.linearCombination K (fun F => a F • scalarCharacterLp K p F) c) =ᵐ[haar]
      fun x => ∑ F ∈ c.support, c F * a F * scalarCharacter K F x := by
  have hh (F : Finset ℕ) : a F • scalarCharacterLp K p F =ᵐ[haar]
      fun x => a F * scalarCharacter K F x := by
    filter_upwards [Lp.coeFn_smul (a F) (scalarCharacterLp K p F),
      coeFn_scalarCharacterLp K p F] with x hs hc
    simp only [hs, Pi.smul_apply, hc, smul_eq_mul]
  filter_upwards [Lp.coeFn_linearCombination c (fun F => a F • scalarCharacterLp K p F),
    ae_all_iff.mpr hh] with x hx hall
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hall, mul_assoc] using hx

theorem coeFn_polynomialLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Coefficients K) :
    polynomialLp K p c =ᵐ[haar]
      fun x => ∑ F ∈ c.support, c F * scalarCharacter K F x := by
  simpa only [one_smul, mul_one, polynomialLp] using
    coeFn_weighted_polynomial K p (fun _ => 1) c

theorem coeFn_noisePolynomial (u : ℝ≥0) (c : Coefficients K) :
    noisePolynomial K u c =ᵐ[haar]
      fun x => ∑ F ∈ c.support, c F * ((Real.exp (-(u : ℝ) * F.card) : ℝ) : K) *
        scalarCharacter K F x :=
  coeFn_weighted_polynomial K 2 (fun F => ((Real.exp (-(u : ℝ) * F.card) : ℝ) : K)) c

theorem norm_sq_eq_integral_rpow (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp K p haar) {g : Group → K} (hfg : f =ᵐ[haar] g) :
    ‖f‖ ^ 2 = (∫ x, ‖g x‖ ^ p.toReal ∂haar) ^ (2 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hi : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂haar := integral_nonneg (fun x => by positivity)
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm hp0 hp (Lp.memLp f),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hi _), ← Real.rpow_two,
    ← Real.rpow_mul hi]
  have he : p.toReal⁻¹ * 2 = 2 / p.toReal := by ring
  rw [he]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem real_polynomial_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp2 : p.toReal ≤ 2) (u : ℝ≥0)
    (hu : (Real.exp (-(u : ℝ))) ^ 2 ≤ p.toReal - 1) :
    PolynomialBound ℝ p u := by
  intro c
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_integral_rpow ℝ 2 (by norm_num) _ (coeFn_noisePolynomial ℝ u c),
    norm_sq_eq_integral_rpow ℝ p hp _ (coeFn_polynomialLp ℝ p c)]
  simp only [ENNReal.toReal_ofNat, div_self (show (2 : ℝ) ≠ 0 by norm_num),
    Real.rpow_one, Real.rpow_two, Real.norm_eq_abs, sq_abs, scalarCharacter]
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have h := Bonami.finite_walsh_sum_bound p.toReal (Real.exp (-(u : ℝ))) hp1 hp2 hu c.support c
  have he (F : Finset ℕ) : Real.exp (-(u : ℝ)) ^ F.card =
      Real.exp (-(u : ℝ) * F.card) := by rw [← Real.exp_nat_mul]; congr 1; ring
  simpa [he] using h

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp2 : p.toReal ≤ 2)
  (u : ℝ≥0) (hu : (Real.exp (-(u : ℝ))) ^ 2 ≤ p.toReal - 1)

/-- The actual constant-rate noise, extended from Haar Lp into Haar L2.
All finite-dimensional and real-to-complex estimates are discharged. -/
def noiseLpToL2 : Lp K p haar →L[K] Lp K 2 haar :=
  scalarLift K p (measure constantRates u) (polynomialExtension ℝ p u)
    (polynomialExtension_overlap ℝ p hp u (real_polynomial_bound p hp hp2 u hu))

theorem norm_noiseLpToL2_le_one : ‖noiseLpToL2 K p hp hp2 u hu‖ ≤ 1 :=
  (norm_scalarLift_le K p (measure constantRates u) (polynomialExtension ℝ p u)
    (polynomialExtension_overlap ℝ p hp u (real_polynomial_bound p hp hp2 u hu))).trans
      (norm_polynomialExtension_le_one ℝ p hp u (real_polynomial_bound p hp hp2 u hu))

theorem noiseLpToL2_overlap (f : Lp K p haar) :
    l2ToL1 (noiseLpToL2 K p hp hp2 u hu f) =
      noiseL1 K constantRates u (ProbabilityLp.inclusion haar 1 p (Fact.out : 1 ≤ p) f) :=
  scalarLift_overlap K p (measure constantRates u) (polynomialExtension ℝ p u)
    (polynomialExtension_overlap ℝ p hp u (real_polynomial_bound p hp hp2 u hu)) f

/-- The sharp input exponent for a specified nonnegative time. -/
def exponent (u : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (1 + Real.exp (-2 * (u : ℝ)))

theorem exponent_ge_one (u : ℝ≥0) : 1 ≤ exponent u := by
  rw [exponent, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (Real.exp_nonneg _))

instance exponent_fact (u : ℝ≥0) : Fact (1 ≤ exponent u) := ⟨exponent_ge_one u⟩

@[simp] theorem exponent_ne_top (u : ℝ≥0) : exponent u ≠ ∞ := ENNReal.ofReal_ne_top

@[simp] theorem exponent_toReal (u : ℝ≥0) :
    (exponent u).toReal = 1 + Real.exp (-2 * (u : ℝ)) := by
  exact ENNReal.toReal_ofReal (by positivity)

theorem exponent_toReal_le_two (u : ℝ≥0) : (exponent u).toReal ≤ 2 := by
  rw [exponent_toReal]
  have he : Real.exp (-2 * (u : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) u.coe_nonneg)
  linarith

theorem exponent_lt_two (u : ℝ≥0) (hu : 0 < u) : exponent u < 2 := by
  rw [exponent, ← ENNReal.ofReal_ofNat 2]
  have hur : 0 < (u : ℝ) := hu
  have he : Real.exp (-2 * (u : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by linarith)

theorem exponent_noise_condition (u : ℝ≥0) :
    (Real.exp (-(u : ℝ))) ^ 2 ≤ (exponent u).toReal - 1 := by
  rw [exponent_toReal, add_sub_cancel_left, ← Real.exp_nat_mul]
  apply le_of_eq
  congr 1
  norm_num

/-- A concrete dimension-independent Lp-L2 contraction at every positive time,
with the displayed sharp exponent strictly below two. -/
def positiveTimeNoiseL2 (u : ℝ≥0) : Lp K (exponent u) haar →L[K] Lp K 2 haar :=
  noiseLpToL2 K (exponent u) (exponent_ne_top u) (exponent_toReal_le_two u) u
    (exponent_noise_condition u)

theorem norm_positiveTimeNoiseL2_le_one (u : ℝ≥0) : ‖positiveTimeNoiseL2 K u‖ ≤ 1 :=
  norm_noiseLpToL2_le_one K (exponent u) (exponent_ne_top u) (exponent_toReal_le_two u) u
    (exponent_noise_condition u)

theorem positiveTimeNoiseL2_overlap (u : ℝ≥0) (f : Lp K (exponent u) haar) :
    l2ToL1 (positiveTimeNoiseL2 K u f) = noiseL1 K constantRates u
      (ProbabilityLp.inclusion haar 1 (exponent u) (exponent_ge_one u) f) :=
  noiseLpToL2_overlap K (exponent u) (exponent_ne_top u) (exponent_toReal_le_two u) u
    (exponent_noise_condition u) f

#print axioms noiseLpToL2_overlap
#print axioms norm_positiveTimeNoiseL2_le_one
#print axioms positiveTimeNoiseL2_overlap

end PL1.NoiseHypercontractivity
