import PL1CD.EntropyAverage
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace PL1CD.Entropy

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  (μ : Measure Ω) [IsFiniteMeasure μ]

def lpAverage (f : ι → Lp ℝ 1 μ) : Lp ℝ 1 μ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, f i

theorem bounded_lp_average_entropy_gap (f : ι → Lp ℝ 1 μ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ x ∂μ, f i x ∈ Set.Icc 0 C)
    (hmass : ∀ i, ∫ x, f i x ∂μ ≤ 1) :
    (Fintype.card ι : ℝ)⁻¹ * (∑ i, Phi μ (f i)) - Phi μ (lpAverage μ f) ≥
      (4 * (Fintype.card ι : ℝ))⁻¹ * ∑ i, ‖f i - lpAverage μ f‖ ^ 2 := by
  classical
  let good : Set Ω := {x | ∀ i, f i x ∈ Set.Icc 0 C}
  have hgood : MeasurableSet good := by
    simp only [good, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact isClosed_Icc.measurableSet.preimage (Lp.stronglyMeasurable (f i)).measurable
  let p : ι → Ω → ℝ := fun i x => if x ∈ good then f i x else 0
  have hp (i : ι) : Measurable (p i) :=
    Measurable.ite hgood (Lp.stronglyMeasurable (f i)).measurable measurable_const
  have hpb (i : ι) (x : Ω) : p i x ∈ Set.Icc 0 C := by
    by_cases hx : x ∈ good
    · simpa only [p, ite_eq_left hx] using hx i
    · simpa only [p, ite_eq_right hx, Set.mem_Icc, le_refl, true_and] using hC
  have hpae (i : ι) : f i =ᵐ[μ] p i := by
    filter_upwards [eventually_countable_forall.mpr hbound] with x hx
    exact (ite_eq_left hx).symm
  have hg : lpAverage μ f =ᵐ[μ] functionAverage p := by
    filter_upwards [Lp.coeFn_smul (Fintype.card ι : ℝ)⁻¹ (∑ i, f i),
      Lp.coeFn_finsetSum Finset.univ f, eventually_countable_forall.mpr hpae] with x hs hsum hx
    change lpAverage μ f x = _
    change ((Fintype.card ι : ℝ)⁻¹ • ∑ i, f i) x = _
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, hsum, Finset.sum_apply]
    unfold functionAverage
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hx i)
  have hpm (i : ι) : ∫ x, p i x ∂μ ≤ 1 := by
    rw [← integral_congr_ae (hpae i)]
    exact hmass i
  have hPi (i : ι) : Phi μ (f i) = Phi μ (p i) :=
    integral_congr_ae ((hpae i).fun_comp phi)
  have hPg : Phi μ (lpAverage μ f) = Phi μ (functionAverage p) :=
    integral_congr_ae (hg.fun_comp phi)
  have hn (i : ι) : ‖f i - lpAverage μ f‖ =
      ∫ x, |p i x - functionAverage p x| ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f i) (lpAverage μ f), hpae i, hg] with x hx hf hav
    simp only [hx, Pi.sub_apply, hf, hav, Real.norm_eq_abs]
  have h := bounded_average_entropy_gap μ p hp C hpb hpm
  simpa only [hPi, hPg, hn] using h

end PL1CD.Entropy
