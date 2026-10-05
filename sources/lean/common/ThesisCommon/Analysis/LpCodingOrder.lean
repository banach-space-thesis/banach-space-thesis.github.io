import ThesisCommon.Analysis.LpMeasureCoding
import Mathlib.MeasureTheory.Function.LpOrder

/-! The actual real Lp lattice and its transport through measurable codings.
These results use mathlib's order on a.e. equivalence classes. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable (μ : Measure X) (f : X → Y) (hf : Measurable f) (hgen : mY.comap f = mX)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem lpComapEquiv_le_iff (u v : Lp ℝ p (μ.map f)) :
    lpComapEquiv μ f hf hgen p u ≤ lpComapEquiv μ f hf hgen p v ↔ u ≤ v := by
  rw [← Lp.coeFn_le, ← Lp.coeFn_le]
  change (∀ᵐ x ∂μ, (lpComapEquiv μ f hf hgen p u) x ≤
    (lpComapEquiv μ f hf hgen p v) x) ↔ ∀ᵐ y ∂μ.map f, u y ≤ v y
  rw [ae_map_iff hf.aemeasurable
    (measurableSet_le (Lp.stronglyMeasurable u).measurable (Lp.stronglyMeasurable v).measurable)]
  constructor
  · intro h
    filter_upwards [h, lpComapEquiv_coe μ f hf hgen p u,
      lpComapEquiv_coe μ f hf hgen p v] with x hx hu hv
    simpa only [hu, hv, Function.comp_apply] using hx
  · intro h
    filter_upwards [h, lpComapEquiv_coe μ f hf hgen p u,
      lpComapEquiv_coe μ f hf hgen p v] with x hx hu hv
    simpa only [hu, hv, Function.comp_apply] using hx

/-- The same coding isometry with its genuine order-isomorphism structure. -/
def lpComapOrderIso (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (hgen : mY.comap f = mX) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp ℝ p (μ.map f) ≃o Lp ℝ p μ where
  toEquiv := (lpComapEquiv μ f hf hgen p).toEquiv
  map_rel_iff' := fun {u v} => lpComapEquiv_le_iff μ f hf hgen p u v

theorem lpComapEquiv_sup (u v : Lp ℝ p (μ.map f)) :
    lpComapEquiv μ f hf hgen p (u ⊔ v) =
      lpComapEquiv μ f hf hgen p u ⊔ lpComapEquiv μ f hf hgen p v :=
  (lpComapOrderIso μ f hf hgen p).map_sup u v

theorem lpComapEquiv_inf (u v : Lp ℝ p (μ.map f)) :
    lpComapEquiv μ f hf hgen p (u ⊓ v) =
      lpComapEquiv μ f hf hgen p u ⊓ lpComapEquiv μ f hf hgen p v :=
  (lpComapOrderIso μ f hf hgen p).map_inf u v

theorem lpComapEquiv_abs (u : Lp ℝ p (μ.map f)) :
    lpComapEquiv μ f hf hgen p |u| = |lpComapEquiv μ f hf hgen p u| := by
  change lpComapEquiv μ f hf hgen p (u ⊔ -u) =
    lpComapEquiv μ f hf hgen p u ⊔ -(lpComapEquiv μ f hf hgen p u)
  rw [lpComapEquiv_sup, map_neg]

omit [MeasurableSpace Y] [Fact (1 ≤ p)] in
/-- Norm additivity on the positive cone of the genuine real L¹ lattice. -/
theorem lOne_norm_add_of_nonneg (u v : Lp ℝ 1 μ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ‖u + v‖ = ‖u‖ + ‖v‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖(u + v) x‖ ∂μ) = ∫ x, ‖u x‖ + ‖v x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add u v, (Lp.coeFn_nonneg u).mpr hu,
        (Lp.coeFn_nonneg v).mpr hv] with x hadd hux hvx
      simp only [Pi.add_apply] at hadd
      rw [hadd, Real.norm_of_nonneg hux, Real.norm_of_nonneg hvx,
        Real.norm_of_nonneg (add_nonneg hux hvx)]
    _ = (∫ x, ‖u x‖ ∂μ) + ∫ x, ‖v x‖ ∂μ :=
      integral_add (L1.integrable_coeFn u).norm (L1.integrable_coeFn v).norm

end ThesisCommon
