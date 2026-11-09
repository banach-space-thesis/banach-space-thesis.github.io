import PL1.WalshModel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.RCLike.Basic

/-!
# Probability convolution on the actual Haar L1 space

The construction uses a product measure and Fubini, so it acts on genuine L1
equivalence classes. It applies to arbitrary probability measures, including
measures singular with respect to Haar measure.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace PL1.Walsh

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Every element of the sign group is its own inverse. -/
@[simp] theorem group_inv_eq_self (x : Group) : x⁻¹ = x := by
  funext j
  exact congrArg Multiplicative.ofAdd (ZMod.neg_eq_self_mod_two (x j).toAdd)

/-- Multiplication sends Haar × ν to Haar when ν is a probability measure. -/
theorem measurePreserving_multiply (ν : Measure Group) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : Group × Group => z.1 * z.2) (haar.prod ν) haar :=
  measurePreserving_fst.comp (measurePreserving_mul_prod haar ν)

/-- The scalar integral representative used in probability convolution. -/
def convolutionFunction (ν : Measure Group) (f : Lp 𝕜 1 haar) (x : Group) : 𝕜 :=
  ∫ y, f (x * y) ∂ν

theorem integrable_convolution_integrand (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) :
    Integrable (fun z : Group × Group => f (z.1 * z.2)) (haar.prod ν) :=
  (measurePreserving_multiply ν).integrable_comp_of_integrable (L1.integrable_coeFn f)

theorem integrable_convolutionFunction (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) : Integrable (convolutionFunction ν f) haar :=
  (integrable_convolution_integrand ν f).integral_prod_left

/-- Probability convolution as a function between actual L1 quotient spaces. -/
def convolutionL1Fun (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) : Lp 𝕜 1 haar :=
  (integrable_convolutionFunction ν f).toL1 (convolutionFunction ν f)

theorem coeFn_convolutionL1Fun (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) :
    convolutionL1Fun ν f =ᵐ[haar] convolutionFunction ν f :=
  (integrable_convolutionFunction ν f).coeFn_toL1

theorem convolutionFunction_add (ν : Measure Group) [IsProbabilityMeasure ν]
    (f g : Lp 𝕜 1 haar) :
    convolutionFunction ν (f + g) =ᵐ[haar]
      fun x => convolutionFunction ν f x + convolutionFunction ν g x := by
  have hae := (measurePreserving_multiply ν).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_add f g)
  filter_upwards [ae_ae_of_ae_prod hae,
    (integrable_convolution_integrand ν f).prod_right_ae,
    (integrable_convolution_integrand ν g).prod_right_ae] with x hx hf hg
  change (∫ y, (f + g) (x * y) ∂ν) = _
  calc
    _ = ∫ y, (f (x * y) + g (x * y)) ∂ν := integral_congr_ae hx
    _ = _ := integral_add hf hg

theorem convolutionFunction_smul (ν : Measure Group) [IsProbabilityMeasure ν]
    (c : 𝕜) (f : Lp 𝕜 1 haar) :
    convolutionFunction ν (c • f) =ᵐ[haar] fun x => c • convolutionFunction ν f x := by
  have hae := (measurePreserving_multiply ν).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_smul c f)
  filter_upwards [ae_ae_of_ae_prod hae] with x hx
  change (∫ y, (c • f) (x * y) ∂ν) = _
  calc
    _ = ∫ y, c • f (x * y) ∂ν := integral_congr_ae hx
    _ = _ := integral_smul c _

theorem convolutionL1Fun_add (ν : Measure Group) [IsProbabilityMeasure ν]
    (f g : Lp 𝕜 1 haar) :
    convolutionL1Fun ν (f + g) = convolutionL1Fun ν f + convolutionL1Fun ν g := by
  apply Lp.ext
  filter_upwards [coeFn_convolutionL1Fun ν (f + g), coeFn_convolutionL1Fun ν f,
    coeFn_convolutionL1Fun ν g, convolutionFunction_add ν f g,
    Lp.coeFn_add (convolutionL1Fun ν f) (convolutionL1Fun ν g)] with x hfg hf hg hconv hadd
  simpa only [hfg, hadd, Pi.add_apply, hf, hg] using hconv

theorem convolutionL1Fun_smul (ν : Measure Group) [IsProbabilityMeasure ν]
    (c : 𝕜) (f : Lp 𝕜 1 haar) :
    convolutionL1Fun ν (c • f) = c • convolutionL1Fun ν f := by
  apply Lp.ext
  filter_upwards [coeFn_convolutionL1Fun ν (c • f), coeFn_convolutionL1Fun ν f,
    convolutionFunction_smul ν c f, Lp.coeFn_smul c (convolutionL1Fun ν f)] with x hcf hf hconv hsmul
  simpa only [hcf, hf, hsmul, Pi.smul_apply] using hconv

/-- Convolution by a probability measure is an L1 contraction. -/
theorem norm_convolutionL1Fun_le (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) : ‖convolutionL1Fun ν f‖ ≤ ‖f‖ := by
  have hprod := integrable_convolution_integrand ν f
  have hmap : AEStronglyMeasurable (fun x => ‖f x‖)
      (Measure.map (fun z : Group × Group => z.1 * z.2) (haar.prod ν)) := by
    rw [(measurePreserving_multiply ν).map_eq]
    exact (Lp.aestronglyMeasurable f).norm
  calc
    ‖convolutionL1Fun ν f‖ = ∫ x, ‖convolutionFunction ν f x‖ ∂haar :=
      L1.norm_of_fun_eq_integral_norm (integrable_convolutionFunction ν f)
    _ ≤ ∫ x, ∫ y, ‖f (x * y)‖ ∂ν ∂haar := by
      apply integral_mono (integrable_convolutionFunction ν f).norm hprod.integral_norm_prod_left
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ z : Group × Group, ‖f (z.1 * z.2)‖ ∂(haar.prod ν) :=
      integral_integral hprod.norm
    _ = ∫ x, ‖f x‖ ∂haar := by
      have h := integral_map (measurePreserving_multiply ν).measurable.aemeasurable hmap
      rw [(measurePreserving_multiply ν).map_eq] at h
      exact h.symm
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

/-- The bounded linear probability-convolution operator used by the construction. -/
def convolutionL1 (ν : Measure Group) [IsProbabilityMeasure ν] :
    Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar :=
  LinearMap.mkContinuous
    { toFun := convolutionL1Fun ν
      map_add' := convolutionL1Fun_add ν
      map_smul' := convolutionL1Fun_smul ν }
    1 (fun f => by
      change ‖convolutionL1Fun ν f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_convolutionL1Fun_le ν f)

theorem convolutionL1_apply (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) : convolutionL1 ν f = convolutionL1Fun ν f := rfl

theorem coeFn_convolutionL1 (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) :
    convolutionL1 ν f =ᵐ[haar] fun x => ∫ y, f (x * y) ∂ν :=
  coeFn_convolutionL1Fun ν f

theorem norm_convolutionL1_le_one (ν : Measure Group) [IsProbabilityMeasure ν] :
    ‖convolutionL1 (𝕜 := 𝕜) ν‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [convolutionL1_apply, one_mul] using norm_convolutionL1Fun_le ν f

/-- Any representative of an L1 class gives the same convolution almost everywhere,
even when the convolving measure is singular. -/
theorem convolutionL1_ae_eq_integral_of_ae_eq (ν : Measure Group) [IsProbabilityMeasure ν]
    {f : Lp 𝕜 1 haar} {g : Group → 𝕜} (hfg : f =ᵐ[haar] g) :
    convolutionL1 ν f =ᵐ[haar] fun x => ∫ y, g (x * y) ∂ν := by
  have hae := (measurePreserving_multiply ν).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [coeFn_convolutionL1 ν f, ae_ae_of_ae_prod hae] with x hx hxy
  exact hx.trans (integral_congr_ae hxy)

/-- The quotient construction agrees with the raw convolution definition already
used for real-valued Walsh characters. -/
theorem convolutionL1_ae_eq_convolution (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp ℝ 1 haar) : convolutionL1 ν f =ᵐ[haar] convolution ν f := by
  filter_upwards [coeFn_convolutionL1 ν f] with x hx
  change convolutionL1 ν f x = ∫ y, f (x * y⁻¹) ∂ν
  simpa only [group_inv_eq_self] using hx

/-- Convolution by a probability measure preserves the Haar integral. -/
theorem integral_convolutionL1 (ν : Measure Group) [IsProbabilityMeasure ν]
    (f : Lp 𝕜 1 haar) :
    ∫ x, convolutionL1 ν f x ∂haar = ∫ x, f x ∂haar := by
  have hmap : AEStronglyMeasurable (fun x => f x)
      (Measure.map (fun z : Group × Group => z.1 * z.2) (haar.prod ν)) := by
    rw [(measurePreserving_multiply ν).map_eq]
    exact Lp.aestronglyMeasurable f
  calc
    _ = ∫ x, ∫ y, f (x * y) ∂ν ∂haar := integral_congr_ae (coeFn_convolutionL1 ν f)
    _ = ∫ z : Group × Group, f (z.1 * z.2) ∂(haar.prod ν) :=
      integral_integral (integrable_convolution_integrand ν f)
    _ = _ := by
      have h := integral_map (measurePreserving_multiply ν).measurable.aemeasurable hmap
      rw [(measurePreserving_multiply ν).map_eq] at h
      exact h.symm

/-- The real Walsh eigenvalue formula for the actual L1 convolution operator. -/
theorem convolutionL1_character (ν : Measure Group) [IsProbabilityMeasure ν]
    (F : Finset ℕ) :
    convolutionL1 ν (characterLp 1 F) = coefficient ν F • characterLp 1 F := by
  apply Lp.ext
  filter_upwards [convolutionL1_ae_eq_integral_of_ae_eq ν (coeFn_characterLp 1 F),
    Lp.coeFn_smul (coefficient ν F) (characterLp 1 F), coeFn_characterLp 1 F]
      with x hconv hsmul hchar
  rw [hconv, hsmul, Pi.smul_apply, hchar]
  simp only [character_mul, integral_const_mul, coefficient, smul_eq_mul, mul_comm]

/-- The same eigenvalue formula over either scalar field, with the real Fourier
coefficient explicitly embedded into the selected RCLike field. -/
theorem convolutionL1_scalarCharacter (ν : Measure Group) [IsProbabilityMeasure ν]
    (F : Finset ℕ) :
    convolutionL1 ν (scalarCharacterLp 𝕜 1 F) =
      (coefficient ν F : 𝕜) • scalarCharacterLp 𝕜 1 F := by
  apply Lp.ext
  filter_upwards [convolutionL1_ae_eq_integral_of_ae_eq ν (coeFn_scalarCharacterLp 𝕜 1 F),
    Lp.coeFn_smul (coefficient ν F : 𝕜) (scalarCharacterLp 𝕜 1 F),
    coeFn_scalarCharacterLp 𝕜 1 F] with x hconv hsmul hchar
  rw [hconv, hsmul, Pi.smul_apply, hchar]
  simp only [scalarCharacter, character_mul, RCLike.ofReal_mul, integral_const_mul,
    integral_ofReal, coefficient, smul_eq_mul, mul_comm]

/-- Continuous linear maps on Haar L1 are determined by their Walsh values. -/
theorem continuousLinearMap_ext_on_scalarCharacterL1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {S T : Lp 𝕜 1 haar →L[𝕜] E}
    (h : ∀ F : Finset ℕ, S (scalarCharacterLp 𝕜 1 F) = T (scalarCharacterLp 𝕜 1 F)) :
    S = T := by
  apply ContinuousLinearMap.ext_on (dense_span_scalarCharacterLp 𝕜 1 (by norm_num))
  rintro x ⟨F, rfl⟩
  exact h F

/-- Equality of Walsh coefficients implies equality of the probability convolution operators. -/
theorem convolutionL1_eq_of_coefficients_eq
    (ν ρ : Measure Group) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (h : ∀ F : Finset ℕ, coefficient ν F = coefficient ρ F) :
    convolutionL1 (𝕜 := 𝕜) ν = convolutionL1 ρ := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  rw [convolutionL1_scalarCharacter, convolutionL1_scalarCharacter, h F]

/-- A product identity for Walsh coefficients induces the corresponding operator
composition identity. This is useful for the noise semigroup. -/
theorem convolutionL1_comp_eq_of_coefficients
    (ν ρ τ : Measure Group) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure τ]
    (h : ∀ F : Finset ℕ, coefficient τ F = coefficient ν F * coefficient ρ F) :
    (convolutionL1 (𝕜 := 𝕜) ν).comp (convolutionL1 ρ) = convolutionL1 τ := by
  apply continuousLinearMap_ext_on_scalarCharacterL1
  intro F
  simp only [ContinuousLinearMap.comp_apply, convolutionL1_scalarCharacter, map_smul,
    h F, RCLike.ofReal_mul, smul_smul, mul_comm]

end PL1.Walsh
