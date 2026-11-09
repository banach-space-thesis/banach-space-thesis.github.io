import PL1.WalshModel
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The actual product noise measures

For nonnegative coordinate rates and nonnegative time, each coordinate is a
two-point probability with mean exp(-u*lambda_j). The measure on the countable
sign group is Mathlib's countable product probability, not an abstract Fourier
multiplier. Coordinates are zero based throughout.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace PL1.Noise

open Walsh

/-- The two rate choices in the manuscript. -/
def schurRates (j : ℕ) : ℝ≥0 := ⟨Real.sqrt (Real.log (j + 2)), Real.sqrt_nonneg _⟩

def constantRates (_ : ℕ) : ℝ≥0 := 1

/-- Coordinate expectation at time u. -/
def bias (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) : ℝ :=
  Real.exp (-(u : ℝ) * rates j)

theorem bias_pos (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) : 0 < bias rates u j :=
  Real.exp_pos _

theorem bias_le_one (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) : bias rates u j ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr u.coe_nonneg) (rates j).coe_nonneg

def positiveProbability (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) : unitInterval :=
  ⟨(1 + bias rates u j) / 2, by
    constructor
    · have := bias_pos rates u j
      linarith
    · have := bias_le_one rates u j
      linarith⟩

/-- The actual biased probability on one sign coordinate. -/
def coordinateMeasure (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) : Measure Sign :=
  bernoulliMeasure 1 (Multiplicative.ofAdd 1) (positiveProbability rates u j)

instance (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) :
    IsProbabilityMeasure (coordinateMeasure rates u j) := by
  unfold coordinateMeasure
  infer_instance

/-- The countable product probability mu_u of the manuscript. -/
def measure (rates : ℕ → ℝ≥0) (u : ℝ≥0) : Measure Walsh.Group :=
  Measure.infinitePi (coordinateMeasure rates u)

instance (rates : ℕ → ℝ≥0) (u : ℝ≥0) : IsProbabilityMeasure (measure rates u) := by
  unfold measure
  infer_instance

theorem integral_signValue (rates : ℕ → ℝ≥0) (u : ℝ≥0) (j : ℕ) :
    ∫ a, signValue a ∂coordinateMeasure rates u j = bias rates u j := by
  rw [coordinateMeasure, integral_bernoulliMeasure]
  norm_num [signValue, positiveProbability]
  ring

/-- The sum of rates over a finite Walsh support. -/
def rateSum (rates : ℕ → ℝ≥0) (F : Finset ℕ) : ℝ := ∑ j ∈ F, (rates j : ℝ)

theorem rateSum_nonneg (rates : ℕ → ℝ≥0) (F : Finset ℕ) : 0 ≤ rateSum rates F :=
  Finset.sum_nonneg (fun j _ => (rates j).coe_nonneg)

/-- Independence gives the Fourier transform of the actual product measure. -/
theorem integral_character (rates : ℕ → ℝ≥0) (u : ℝ≥0) (F : Finset ℕ) :
    ∫ x, character F x ∂measure rates u = Real.exp (-(u : ℝ) * rateSum rates F) := by
  have heq (x : Walsh.Group) : character F x = ∏ j : F, signValue (x j) := by
    exact (Finset.prod_coe_sort F (fun j => signValue (x j))).symm
  simp_rw [heq]
  change (∫ x, (fun y : F → Sign => ∏ j, signValue (y j)) (F.restrict x)
    ∂Measure.infinitePi (coordinateMeasure rates u)) = _
  rw [integral_restrict_infinitePi (coordinateMeasure rates u)
    (s := F) (f := fun y : F → Sign => ∏ j, signValue (y j))
      (continuous_of_discreteTopology.aestronglyMeasurable),
    integral_fintype_prod_eq_prod]
  simp_rw [integral_signValue]
  rw [Finset.prod_coe_sort]
  simp only [bias]
  rw [← Real.exp_sum]
  congr 1
  simp [rateSum, Finset.mul_sum]

@[simp]
theorem integral_character_constantRates (u : ℝ≥0) (F : Finset ℕ) :
    ∫ x, character F x ∂measure constantRates u = Real.exp (-(u : ℝ) * F.card) := by
  rw [integral_character]
  simp [rateSum, constantRates]

theorem measurable_coordinateMeasure (rates : ℕ → ℝ≥0) (j : ℕ) :
    Measurable (fun u => coordinateMeasure rates u j) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [coordinateMeasure, bernoulliMeasure_apply _ hA]
  split_ifs <;> fun_prop [positiveProbability, bias]

/-- The product probabilities form a measurable family, so averaging them
against a time distribution is an actual measure-theoretic construction. -/
theorem measurable_measure (rates : ℕ → ℝ≥0) : Measurable (measure rates) := by
  classical
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  intro A hA
  obtain ⟨F, B, hB, rfl⟩ := (mem_measurableCylinders A).mp hA
  have hc (u : ℝ≥0) := Measure.infinitePi_cylinder
    (coordinateMeasure rates u) (s := F) (S := B) hB
  simp only [measure, hc]
  have heq (u : ℝ≥0) :
      Measure.pi (fun j : F => coordinateMeasure rates u j) B =
        ∑ x ∈ B.toFinset, ∏ j : F, coordinateMeasure rates u j {x j} := by
    simp only [← Measure.pi_singleton]
    rw [sum_measure_singleton]
    simp only [Set.coe_toFinset]
  simp only [heq]
  apply Finset.measurable_sum
  intro x hx
  apply Finset.measurable_prod
  intro j hj
  exact (Measure.measurable_coe (measurableSet_singleton _)).comp
    (measurable_coordinateMeasure rates j)

/-- The concrete Markov kernel u ↦ mu_u. -/
def kernel (rates : ℕ → ℝ≥0) : Kernel ℝ≥0 Walsh.Group where
  toFun := measure rates
  measurable' := measurable_measure rates

@[simp]
theorem kernel_apply (rates : ℕ → ℝ≥0) (u : ℝ≥0) : kernel rates u = measure rates u := rfl

instance (rates : ℕ → ℝ≥0) : IsMarkovKernel (kernel rates) where
  isProbabilityMeasure u := inferInstanceAs (IsProbabilityMeasure (measure rates u))

end PL1.Noise
