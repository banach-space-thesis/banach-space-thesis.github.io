import PL1.KernelTranslations
import PL1.TailSpikeEvents

/-!
# Actual finite tail-spike families

This is the paper's tail-spike lemma on the original Haar sign group. The
functions and sets depend only on a displayed finite set of coordinates past
the prescribed prefix; they are the pullbacks of the corresponding tail data.
All averages are finite, and the displayed noise operator is the actual one.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PL1.TailSpikes
open Walsh Noise FiniteCoordinateKernels

structure RateFamily (rates : ℕ → ℝ≥0) (d : ℕ) (t : PositiveTime) (δ : ℝ) where
  coordinates : Finset ℕ
  beyond_prefix : Disjoint coordinates (Finset.range d)
  q : Assignments coordinates → C(Walsh.Group, ℝ)
  B : Assignments coordinates → Set Walsh.Group
  q_depends : ∀ a x y, (∀ j ∈ coordinates, x j = y j) → q a x = q a y
  B_depends : ∀ a, DependsOn coordinates (B a)
  nonnegative : ∀ a x, 0 ≤ q a x
  integral_one : ∀ a, ∫ x, q a x ∂haar = 1
  measurable : ∀ a, MeasurableSet (B a)
  small : ∀ a, haar.real (B a) < δ
  concentrated : ∀ a, 1 - δ < ∫ x in B a, q a x ∂haar
  average_one : ∀ x, (Fintype.card (Assignments coordinates) : ℝ)⁻¹ * ∑ a, q a x = 1
  almost_invariant : ∀ a (u : ℝ≥0),
    ‖noiseL1 ℝ rates u (ContinuousMap.toLp 1 haar ℝ (q a)) -
      ContinuousMap.toLp 1 haar ℝ (q a)‖ ≤ 2 * (1 - Real.exp (-(u : ℝ) / (t : ℝ)))

abbrev Family (d : ℕ) (t : PositiveTime) (δ : ℝ) := RateFamily schurRates d t δ

/-- Finite-coordinate concentration events give the full translated family. -/
theorem exists_rateFamily_of_event (rates : ℕ → ℝ≥0) (d : ℕ) (t : PositiveTime) (δ : ℝ)
    (hEvent : ∃ (S : Finset ℕ) (B : Set Walsh.Group),
      Disjoint S (Finset.range d) ∧ MeasurableSet B ∧ DependsOn S B ∧
      haar.real B < δ ∧ 1 - δ < (resolventMeasure rates t).real B) :
    Nonempty (RateFamily rates d t δ) := by
  let := isProbabilityMeasure_resolventMeasure rates t.property
  obtain ⟨S, B, hSd, hBm, hBS, hBsmall, hBmass⟩ :=
    hEvent
  refine ⟨{
    coordinates := S
    beyond_prefix := hSd
    q := fun a => translatedDensity (resolventMeasure rates t) S (extend S a)
    B := fun a => translatedSet B (extend S a)
    q_depends := fun a _ _ hxy => translatedDensity_congr _ S (extend S a) hxy
    B_depends := fun a => dependsOn_translatedSet S hBS (extend S a)
    nonnegative := fun a => translatedDensity_nonneg _ S (extend S a)
    integral_one := fun a => integral_translatedDensity _ S (extend S a)
    measurable := fun a => measurableSet_translatedSet hBm (extend S a)
    small := ?_
    concentrated := ?_
    average_one := average_translatedDensity _ S
    almost_invariant := fun a u => norm_noise_translatedResolventDensity_sub_le rates t S (extend S a) u
  }⟩
  · intro a
    simpa only [measureReal_def, measure_translatedSet hBm] using hBsmall
  · intro a
    rw [setIntegral_translatedDensity _ S hBm hBS]
    exact hBmass

/-- The complete finite tail-spike construction, with no unproved concentration
or smoothing premises. Positivity of δ is sufficient for the construction. -/
theorem exists_family (d : ℕ) (t : PositiveTime) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (Family d t δ) :=
  exists_rateFamily_of_event schurRates d t δ (TailSpikeEvents.exists_finite_tail_event d t hδ)

theorem RateFamily.almost_invariant_time {rates : ℕ → ℝ≥0} {d : ℕ} {t : PositiveTime} {δ : ℝ}
    (Q : RateFamily rates d t δ) (a : Assignments Q.coordinates) (u : ℝ≥0) :
    ‖noiseL1 ℝ rates u (ContinuousMap.toLp 1 haar ℝ (Q.q a)) -
      ContinuousMap.toLp 1 haar ℝ (Q.q a)‖ ≤ 2 * (u : ℝ) / (t : ℝ) :=
  (Q.almost_invariant a u).trans (by
    have h := one_sub_exp_neg_div_le t u
    convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1
    ring)

end PL1.TailSpikes
