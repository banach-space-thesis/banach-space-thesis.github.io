import ThesisCommon.Analysis.ComplexL1Coordinates

/-! Almost-everywhere scalar disjointness implies disjointness of the actual
real L1 lattice moduli, for both real and complex inputs. -/
noncomputable section
open MeasureTheory Filter
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lOne_abs_inf_eq_zero_of_ae_disjoint (f g : Lp ℝ 1 μ)
    (h : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) : |f| ⊓ |g| = 0 := by
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_abs f, Lp.coeFn_abs g,
    Lp.coeFn_inf |f| |g|, Lp.coeFn_zero ℝ 1 μ] with x hx hf hg hi hz
  rw [hi, Pi.inf_apply, hf, hg, hz, Pi.zero_apply]
  rcases hx with hx | hx <;> simp [hx]

theorem complexL1Modulus_inf_eq_zero_of_ae_disjoint (f g : Lp ℂ 1 μ)
    (h : ∀ᵐ x ∂μ, f x = 0 ∨ g x = 0) :
    complexL1Modulus f ⊓ complexL1Modulus g = 0 := by
  apply Lp.ext
  filter_upwards [h, complexL1Modulus_coe f, complexL1Modulus_coe g,
    Lp.coeFn_inf (complexL1Modulus f) (complexL1Modulus g), Lp.coeFn_zero ℝ 1 μ]
    with x hx hf hg hi hz
  rw [hi, Pi.inf_apply, hf, hg, hz, Pi.zero_apply]
  rcases hx with hx | hx <;> simp [hx]

end ThesisCommon
