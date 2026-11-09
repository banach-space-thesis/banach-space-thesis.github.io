import PL1.EnfloMaxMass
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # A common integrable majorant for the dyadic images of any L1 operator

The sums of the absolute indicator images increase by dyadic refinement.
Their uniformly bounded integrals give a genuine integrable majorant by
monotone convergence, without assuming weak compactness of the operator.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace PL1.EnfloBush

theorem sum_range_double (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n), f j) =
      ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

section General
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Increasing nonnegative integrable functions with bounded integrals have
an actual real-valued integrable majorant, simultaneously almost everywhere. -/
theorem exists_integrable_majorant_of_monotone (f : ℕ → Ω → ℝ)
    (hf : ∀ n, Integrable (f n) μ) (hpos : ∀ n x, 0 ≤ f n x)
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => f n x)) {C : ℝ}
    (hb : ∀ n, ∫ x, f n x ∂μ ≤ C) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ (∀ x, 0 ≤ g x) ∧ ∀ᵐ x ∂μ, ∀ n, f n x ≤ g x := by
  let F : Ω → ℝ≥0∞ := fun x => ⨆ n, ENNReal.ofReal (f n x)
  have hm (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ :=
    (hf n).aemeasurable.ennreal_ofReal
  have hF : AEMeasurable F μ := AEMeasurable.iSup hm
  have hFm : ∀ᵐ x ∂μ, Monotone (fun n => ENNReal.ofReal (f n x)) := by
    filter_upwards [hmono] with x hx
    exact fun n m hnm => ENNReal.ofReal_le_ofReal (hx hnm)
  have hI : (∫⁻ x, F x ∂μ) ≤ ENNReal.ofReal C := by
    rw [show (∫⁻ x, F x ∂μ) = ⨆ n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ from lintegral_iSup' hm hFm]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Filter.Eventually.of_forall (hpos n))]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hIt : (∫⁻ x, F x ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hI
  refine ⟨fun x => (F x).toReal, integrable_toReal_of_lintegral_ne_top hF hIt,
    fun x => ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ae_lt_top' hF hIt] with x hx
  intro n
  have h := ENNReal.toReal_mono hx.ne (le_iSup (fun n => ENNReal.ofReal (f n x)) n)
  simpa only [ENNReal.toReal_ofReal (hpos n x)] using h

end General

section Dyadic
open DyadicTrace
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def dyadicAbsSum (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) (x : Ω) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ n), |T (dyadicVector (𝕜 := ℝ) n j) x|

theorem dyadicAbsSum_nonneg (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) (x : Ω) :
    0 ≤ dyadicAbsSum T n x := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem integrable_dyadicAbsSum (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    Integrable (dyadicAbsSum T n) μ :=
  integrable_finsetSum _ (fun j _ => (L1.integrable_coeFn (T (dyadicVector n j))).abs)

theorem integral_dyadicAbsSum (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    (∫ x, dyadicAbsSum T n x ∂μ) = dyadicSumMass T n := by
  change (∫ x, ∑ j ∈ Finset.range (2 ^ n), |T (dyadicVector (𝕜 := ℝ) n j) x| ∂μ) = _
  rw [integral_finsetSum _ (fun j _ => (L1.integrable_coeFn (T (dyadicVector n j))).abs)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Real.norm_eq_abs] using (L1.norm_eq_integral_norm (T (dyadicVector n j))).symm

theorem dyadicAbsSum_le_succ_ae (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) (n : ℕ) :
    dyadicAbsSum T n ≤ᵐ[μ] dyadicAbsSum T (n + 1) := by
  filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_add
    (T (dyadicVector (n + 1) (2 * j))) (T (dyadicVector (n + 1) (2 * j + 1))))] with x hx
  change (∑ j ∈ Finset.range (2 ^ n), |T (dyadicVector n j) x|) ≤
    ∑ j ∈ Finset.range (2 ^ (n + 1)), |T (dyadicVector (n + 1) j) x|
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ, Nat.mul_comm], sum_range_double]
  apply Finset.sum_le_sum
  intro j _
  rw [dyadicVector_refine, map_add, hx j, Pi.add_apply]
  exact abs_add_le _ _

theorem dyadicAbsSum_monotone_ae (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) :
    ∀ᵐ x ∂μ, Monotone (fun n => dyadicAbsSum T n x) := by
  filter_upwards [ae_all_iff.mpr (dyadicAbsSum_le_succ_ae T)] with x hx
  exact monotone_nat_of_le_succ hx

theorem dyadicSumMass_monotone (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) :
    Monotone (dyadicSumMass T) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [← integral_dyadicAbsSum, ← integral_dyadicAbsSum]
  exact integral_mono_ae (integrable_dyadicAbsSum T n) (integrable_dyadicAbsSum T (n + 1))
    (dyadicAbsSum_le_succ_ae T n)

/-- Every L1 operator has a common integrable bound for all its dyadic
absolute image sums, despite not necessarily being weakly compact. -/
theorem exists_dyadic_majorant (T : IntervalL1 ℝ →L[ℝ] Lp ℝ 1 μ) :
    ∃ g : Ω → ℝ, Integrable g μ ∧ (∀ x, 0 ≤ g x) ∧
      ∀ᵐ x ∂μ, ∀ n, dyadicAbsSum T n x ≤ g x :=
  exists_integrable_majorant_of_monotone (dyadicAbsSum T) (integrable_dyadicAbsSum T)
    (dyadicAbsSum_nonneg T) (dyadicAbsSum_monotone_ae T)
    (fun n => (integral_dyadicAbsSum T n).le.trans (dyadicSumMass_le T n))

end Dyadic

#print axioms exists_dyadic_majorant
end PL1.EnfloBush
