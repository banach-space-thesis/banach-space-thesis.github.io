import JLMS.ScatteredMeasures
import JLMS.L1Restriction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# ℓ¹ coordinates of finite atomic measures

Point masses of an arbitrary finite measure have summable real weights.
For a regular measure on a scattered space, integration is the corresponding
atomic series. This is the measure-to-functional part of Rudin's theorem.
-/

noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal

namespace JLMS

variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K]

theorem summable_measure_pointMass (μ : Measure K) [IsFiniteMeasure μ] :
    Summable (fun x : K => (μ {x}).toReal) := by
  apply ENNReal.summable_toReal
  apply ne_of_lt
  exact (tsum_measure_le_measure_univ
    (fun x => (measurableSet_singleton x).nullMeasurableSet)
    (fun x y hxy => (disjoint_singleton.mpr hxy).aedisjoint)).trans_lt (measure_lt_top μ univ)

/-- The summable list of real point masses, indexed by all points of K. -/
def measureCoordinates (μ : Measure K) [IsFiniteMeasure μ] : ellOneOn ℝ K :=
  ⟨fun x => (μ {x}).toReal, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg] using summable_measure_pointMass μ⟩

@[simp] theorem measureCoordinates_apply (μ : Measure K) [IsFiniteMeasure μ] (x : K) :
    measureCoordinates μ x = (μ {x}).toReal := rfl

variable [TopologicalSpace K] [BorelSpace K] [T2Space K]

/-- Atomicity converts any integrable real function into the point-mass series. -/
theorem integral_eq_tsum_atoms_of_scattered (hK : IsScattered K)
    (μ : Measure K) [IsFiniteMeasure μ] [μ.Regular] (f : K → ℝ) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' x : K, measureCoordinates μ x * f x := by
  classical
  let S : Set K := {x | 0 < μ {x}}
  have heq := measure_eq_sum_atoms_of_scattered hK μ
  have hint : Integrable f (Measure.sum (fun x : S => μ {x.val} • Measure.dirac x.val)) := by
    rw [← heq]
    exact hf
  calc
    ∫ x, f x ∂μ = ∫ x, f x ∂Measure.sum (fun x : S => μ {x.val} • Measure.dirac x.val) :=
      congrArg (fun ν => ∫ x, f x ∂ν) heq
    _ = ∑' x : S, (μ {x.val}).toReal * f x.val := by
      rw [integral_sum_measure hint]
      simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    _ = ∑' x : K, S.indicator (fun x => (μ {x}).toReal * f x) x :=
      tsum_subtype S (fun x => (μ {x}).toReal * f x)
    _ = ∑' x : K, measureCoordinates μ x * f x := by
      congr 1
      funext x
      by_cases hx : x ∈ S
      · simp [hx]
      · have hz : μ {x} = 0 := le_antisymm (le_of_not_gt hx) bot_le
        simp [hx, hz]

end JLMS
