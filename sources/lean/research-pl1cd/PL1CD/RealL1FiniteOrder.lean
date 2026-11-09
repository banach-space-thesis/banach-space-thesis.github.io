import PL1CD.RealL1Order

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace PL1CD.L1Order
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem sum_ae_le_sum (s : Finset ι) (f g : ι → Lp ℝ 1 μ)
    (hfg : ∀ i, ∀ᵐ x ∂μ, f i x ≤ g i x) :
    ∀ᵐ x ∂μ, (∑ i ∈ s, f i) x ≤ (∑ i ∈ s, g i) x := by
  classical
  have he : ∀ᵐ x ∂μ, ∀ i ∈ s, f i x ≤ g i x :=
    s.eventually_all.mpr (fun i _ => hfg i)
  filter_upwards [Lp.coeFn_fun_finsetSum s f, Lp.coeFn_fun_finsetSum s g, he]
    with x hf hg h
  rw [hf, hg]
  exact Finset.sum_le_sum (fun i hi => h i hi)

theorem absL1_sum_le_sum_absL1 (s : Finset ι) (f : ι → Lp ℝ 1 μ) :
    ∀ᵐ x ∂μ, absL1 (∑ i ∈ s, f i) x ≤ (∑ i ∈ s, absL1 (f i)) x := by
  classical
  have he : ∀ᵐ x ∂μ, ∀ i ∈ s, absL1 (f i) x = |f i x| :=
    s.eventually_all.mpr (fun i _ => coeFn_absL1 (f i))
  filter_upwards [coeFn_absL1 (∑ i ∈ s, f i),
    Lp.coeFn_fun_finsetSum s f, Lp.coeFn_fun_finsetSum s (fun i => absL1 (f i)), he]
    with x hab hf hg h
  rw [hab, hf, hg]
  calc
    _ ≤ ∑ i ∈ s, |f i x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun i hi => (h i hi).symm)

end PL1CD.L1Order
