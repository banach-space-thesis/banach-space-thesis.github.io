import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Separation by a nonnegative concentrated density

These estimates use actual measurable sets and Bochner integrals. They apply
to arbitrary probability measures and, in fact, to vectors in any real
normed space. The scalar specialization includes real and complex fields.
-/

noncomputable section
open MeasureTheory

namespace PL1.SpikeSeparation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {q : Ω → ℝ}

theorem integrable_add_smul (hq : Integrable q μ) (b c : E) :
    Integrable (fun x => b + q x • c) μ := (integrable_const b).add (hq.smul_const c)

theorem integrable_norm_add_smul (hq : Integrable q μ) (b c : E) :
    Integrable (fun x => ‖b + q x • c‖) μ := (integrable_add_smul hq b c).norm

private theorem pointwise_left (b c : E) (t : ℝ) (ht : 0 ≤ t) :
    t * ‖c‖ - ‖b‖ ≤ ‖b + t • c‖ := by
  simpa only [norm_neg, sub_neg_eq_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    add_comm] using norm_sub_norm_le (t • c) (-b)

private theorem pointwise_right (b c : E) (t : ℝ) (ht : 0 ≤ t) :
    ‖b‖ - t * ‖c‖ ≤ ‖b + t • c‖ := by
  simpa only [norm_neg, sub_neg_eq_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    using norm_sub_norm_le b (-(t • c))

/-- The two reverse-triangle bounds integrated over a set and its complement. -/
theorem split_estimates (hq : Integrable q μ) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x)
    (B : Set Ω) (b c : E) :
    (∫ x in B, q x ∂μ) * ‖c‖ - μ.real B * ‖b‖ ≤ ∫ x in B, ‖b + q x • c‖ ∂μ ∧
    μ.real Bᶜ * ‖b‖ - (∫ x in Bᶜ, q x ∂μ) * ‖c‖ ≤
      ∫ x in Bᶜ, ‖b + q x • c‖ ∂μ := by
  have hn := integrable_norm_add_smul hq b c
  constructor
  · have h := integral_mono_ae ((hq.mul_const ‖c‖).sub (integrable_const ‖b‖)).integrableOn
      hn.integrableOn (show ∀ᵐ x ∂μ.restrict B, q x * ‖c‖ - ‖b‖ ≤ ‖b + q x • c‖ from by
        filter_upwards [ae_restrict_of_ae hq0] with x hx
        exact pointwise_left b c (q x) hx)
    simpa only [Pi.sub_apply, integral_sub (hq.integrableOn.mul_const ‖c‖) (integrable_const ‖b‖),
      integral_mul_const, integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] using h
  · have h := integral_mono_ae ((integrable_const ‖b‖).sub (hq.mul_const ‖c‖)).integrableOn
      hn.integrableOn (show ∀ᵐ x ∂μ.restrict Bᶜ, ‖b‖ - q x * ‖c‖ ≤ ‖b + q x • c‖ from by
        filter_upwards [ae_restrict_of_ae hq0] with x hx
        exact pointwise_right b c (q x) hx)
    simpa only [Pi.sub_apply, integral_sub (integrable_const ‖b‖) (hq.integrableOn.mul_const ‖c‖),
      integral_mul_const, integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] using h

/-- Exact separation bound obtained by splitting over the concentration set. -/
theorem split_lower_bound (hq : Integrable q μ) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hq1 : ∫ x, q x ∂μ = 1) (B : Set Ω) (hB : MeasurableSet B) (b c : E) :
    (1 - 2 * μ.real B) * ‖b‖ + (2 * (∫ x in B, q x ∂μ) - 1) * ‖c‖ ≤
      ∫ x, ‖b + q x • c‖ ∂μ := by
  obtain ⟨hleft, hright⟩ := split_estimates hq hq0 B b c
  have hmass := integral_add_compl hB hq
  have hmeasure : μ.real B + μ.real Bᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hB
  have hnorm := integral_add_compl hB (integrable_norm_add_smul hq b c)
  rw [hq1] at hmass
  have hm := congrArg (fun t : ℝ => t * ‖c‖) hmass
  have hμ := congrArg (fun t : ℝ => t * ‖b‖) hmeasure
  nlinarith

/-- A unit-mass nonnegative density concentrated on a small set separates all vectors. -/
theorem concentration_lower_bound (hq : Integrable q μ) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hq1 : ∫ x, q x ∂μ = 1) (B : Set Ω) (hB : MeasurableSet B) (δ : ℝ)
    (hsmall : μ.real B ≤ δ) (hconcentrated : 1 - δ ≤ ∫ x in B, q x ∂μ) (b c : E) :
    (1 - 2 * δ) * (‖b‖ + ‖c‖) ≤ ∫ x, ‖b + q x • c‖ ∂μ := by
  have hs := split_lower_bound hq hq0 hq1 B hB b c
  have hb := mul_le_mul_of_nonneg_right (show 1 - 2 * δ ≤ 1 - 2 * μ.real B by linarith)
    (norm_nonneg b)
  have hc := mul_le_mul_of_nonneg_right
    (show 1 - 2 * δ ≤ 2 * (∫ x in B, q x ∂μ) - 1 by linarith) (norm_nonneg c)
  nlinarith

variable {𝕜 : Type*} [RCLike 𝕜]

theorem integrable_norm_add_mul (hq : Integrable q μ) (b c : 𝕜) :
    Integrable (fun x => ‖b + c * (q x : 𝕜)‖) μ := by
  simpa only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal, mul_comm] using
    integrable_norm_add_smul hq b c

/-- The exact scalar inequality used in the manuscript, over both scalar fields. -/
theorem concentration_lower_bound_rclike (hq : Integrable q μ) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hq1 : ∫ x, q x ∂μ = 1) (B : Set Ω) (hB : MeasurableSet B) (δ : ℝ)
    (hsmall : μ.real B ≤ δ) (hconcentrated : 1 - δ ≤ ∫ x in B, q x ∂μ) (b c : 𝕜) :
    (1 - 2 * δ) * (‖b‖ + ‖c‖) ≤ ∫ x, ‖b + c * (q x : 𝕜)‖ ∂μ := by
  simpa only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal, mul_comm] using
    concentration_lower_bound hq hq0 hq1 B hB δ hsmall hconcentrated b c

section Product

variable {H : Type*} [MeasurableSpace H] {ν : Measure H} [SFinite ν]
variable {b c : H → E}

theorem integrable_prod_add_smul (hb : Integrable b ν) (hc : Integrable c ν)
    (hq : Integrable q μ) :
    Integrable (fun z : H × Ω => b z.1 + q z.2 • c z.1) (ν.prod μ) := by
  exact (hb.comp_fst μ).add ((hq.smul_prod hc).swap)

/-- Integrating the scalar/vector separation inequality over independent head coordinates. -/
theorem product_concentration_lower_bound (hb : Integrable b ν) (hc : Integrable c ν)
    (hq : Integrable q μ) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x) (hq1 : ∫ x, q x ∂μ = 1)
    (B : Set Ω) (hB : MeasurableSet B) (δ : ℝ)
    (hsmall : μ.real B ≤ δ) (hconcentrated : 1 - δ ≤ ∫ x in B, q x ∂μ) :
    (1 - 2 * δ) * ((∫ y, ‖b y‖ ∂ν) + ∫ y, ‖c y‖ ∂ν) ≤
      ∫ z : H × Ω, ‖b z.1 + q z.2 • c z.1‖ ∂(ν.prod μ) := by
  have hint := (integrable_prod_add_smul hb hc hq).norm
  rw [integral_prod _ hint]
  have h := integral_mono_ae ((hb.norm.add hc.norm).const_mul (1 - 2 * δ))
    hint.integral_prod_left (Filter.Eventually.of_forall (fun y =>
      concentration_lower_bound hq hq0 hq1 B hB δ hsmall hconcentrated (b y) (c y)))
  simpa only [Pi.add_apply, integral_const_mul, integral_add hb.norm hc.norm] using h

end Product

#print axioms split_lower_bound
#print axioms concentration_lower_bound_rclike
#print axioms product_concentration_lower_bound

end PL1.SpikeSeparation
