import ThesisCommon.Analysis.IntegralKernelModulusBound
import ThesisCommon.Analysis.IntegralKernelPositive
import ThesisCommon.Analysis.IntegralKernelDomination

/-! Identification of the real modulus kernel on arbitrary s-finite
input spaces. Signed-indicator tests give the difficult pointwise bound;
the Riesz--Kantorovich formula gives the reverse bound. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}
variable {k : X × Y → ℝ} {K : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν}

theorem IsIntegralKernel.integrable_abs_section (hk : IsIntegralKernel k K) (f : Lp ℝ 1 μ) :
    ∀ᵐ y ∂ν, Integrable (fun x => |k (x, y)| * f x) μ := by
  filter_upwards [hk.integrable_section f] with y hy
  have hm : Measurable (fun x => |k (x, y)| * f x) :=
    by simpa only [Real.norm_eq_abs] using
      (hk.measurable.comp (measurable_id.prodMk (measurable_const (a := y)))).norm.mul
        (Lp.stronglyMeasurable f).measurable
  apply hy.norm.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs]

theorem IsIntegralKernel.integrable_abs_apply_of_nonneg
    [SFinite μ]
    (hk : IsIntegralKernel k K) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    Integrable (fun y => ∫ x, |k (x, y)| * f x ∂μ) ν := by
  have hm : StronglyMeasurable (fun z : X × Y => |k z| * f z.1) := by
    simpa only [Real.norm_eq_abs] using hk.measurable.norm.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable measurable_fst)
  apply (L1.integrable_coeFn (lOneOperatorModulus K f)).mono'
    hm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [hk.abs_apply_le_modulus f hf] with y hy
  have hn : 0 ≤ ∫ x, |k (x, y)| * f x ∂μ := integral_nonneg_of_ae
    ((Lp.coeFn_nonneg f).mpr hf |>.mono fun x hx => mul_nonneg (abs_nonneg _) hx)
  rw [Real.norm_of_nonneg hn]
  exact hy

theorem IsIntegralKernel.modulus_represents_of_nonneg
    [SFinite μ]
    (hk : IsIntegralKernel k K) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    lOneOperatorModulus K f =ᵐ[ν] fun y => ∫ x, |k (x, y)| * f x ∂μ := by
  let hi := hk.integrable_abs_apply_of_nonneg f hf
  let v : Lp ℝ 1 ν := hi.toL1 (fun y => ∫ x, |k (x, y)| * f x ∂μ)
  have hv : v =ᵐ[ν] fun y => ∫ x, |k (x, y)| * f x ∂μ := Integrable.coeFn_toL1 _
  have hMv : lOneOperatorModulus K f ≤ v := by
    apply (lOneOperatorModulus_rieszKantorovich K f hf).2
    rintro _ ⟨g, hg, rfl⟩
    have hgf : |g| ≤ f := abs_le'.mpr ⟨hg.2, by simpa using neg_le_neg hg.1⟩
    have hgf_ae : ∀ᵐ x ∂μ, |g x| ≤ f x := by
      filter_upwards [(Lp.coeFn_le _ _).mpr hgf, Lp.coeFn_abs g] with x hx habs
      simpa only [habs] using hx
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hk.represents g, hk.integrable_section g, hk.integrable_abs_section f, hv]
      with y hgy hgi hfi hvy
    rw [hgy, hvy]
    calc
      (∫ x, k (x, y) * g x ∂μ) ≤ ∫ x, ‖k (x, y) * g x‖ ∂μ :=
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => k (x, y) * g x))
      _ ≤ ∫ x, |k (x, y)| * f x ∂μ := by
        apply integral_mono_ae hgi.norm hfi
        filter_upwards [hgf_ae] with x hx
        simpa only [Real.norm_eq_abs, abs_mul] using mul_le_mul_of_nonneg_left hx (abs_nonneg (k (x, y)))
  have hvM : v ≤ lOneOperatorModulus K f := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hv, hk.abs_apply_le_modulus f hf] with y hvy hy
    simpa only [hvy] using hy
  rwa [← le_antisymm hMv hvM] at hv

/-- The actual bounded modulus operator has the absolute kernel. The input
measure is s-finite (in particular, sigma-finite); the output is arbitrary. -/
theorem IsIntegralKernel.modulus
    [SFinite μ]
    (hk : IsIntegralKernel k K) : IsIntegralKernel (fun z => |k z|) (lOneOperatorModulus K) where
  measurable := by simpa only [Real.norm_eq_abs] using hk.measurable.norm
  integrable_section := hk.integrable_abs_section
  represents f := by
    have heq : lOneOperatorModulus K f =
        lOneOperatorModulus K f⁺ - lOneOperatorModulus K f⁻ := by
      rw [← map_sub, posPart_sub_negPart]
    have hfcoe : f =ᵐ[μ] fun x => f⁺ x - f⁻ x := by
      have h := Lp.coeFn_sub f⁺ f⁻
      rw [posPart_sub_negPart] at h
      exact h
    filter_upwards [hk.modulus_represents_of_nonneg f⁺ (posPart_nonneg f),
      hk.modulus_represents_of_nonneg f⁻ (negPart_nonneg f),
      Lp.coeFn_sub (lOneOperatorModulus K f⁺) (lOneOperatorModulus K f⁻),
      hk.integrable_abs_section f⁺, hk.integrable_abs_section f⁻] with y hp hn hsub hip hin
    rw [heq, hsub, Pi.sub_apply, hp, hn, ← integral_sub hip hin]
    apply integral_congr_ae
    filter_upwards [hfcoe] with x hx
    rw [hx]
    ring

theorem IsIntegralKernel.abs_hasKernelBound
    [IsFiniteMeasure μ] [SFinite ν]
    (hk : IsIntegralKernel k K) : HasKernelBound μ ν (fun z => |k z|) ‖K‖ := by
  have h := hasKernelBound_of_nonneg hk.modulus (fun z => abs_nonneg (k z))
  rwa [norm_lOneOperatorModulus] at h

theorem IsIntegralKernel.integrable
    [IsFiniteMeasure μ] [SFinite ν]
    (hk : IsIntegralKernel k K) : Integrable k (μ.prod ν) := by
  have hi := integrable_kernel_of_nonneg hk.modulus (fun z => abs_nonneg (k z))
  apply (integrable_norm_iff hk.measurable.aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs] using hi

/-- The sharp column bound for a signed real kernel follows from the
absolute-kernel representation and the norm equality for the modulus. -/
theorem IsIntegralKernel.hasKernelBound
    [IsFiniteMeasure μ] [SFinite ν] (hk : IsIntegralKernel k K) :
    HasKernelBound μ ν k ‖K‖ := by
  apply hk.abs_hasKernelBound.mono hk.measurable
  exact Eventually.of_forall fun x => Eventually.of_forall fun y => by simp

/-- Definition 3.13's actual bounded operator for an arbitrary signed real
kernel, with its column bound derived from the supplied operator. -/
def IsIntegralKernel.truncatedOperator
    [IsFiniteMeasure μ] [SFinite ν] (hk : IsIntegralKernel k K) (r : ℝ) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  truncatedKernelOperator hk.measurable hk.hasKernelBound r

theorem IsIntegralKernel.truncatedOperator_represents
    [IsFiniteMeasure μ] [SFinite ν] (hk : IsIntegralKernel k K) (r : ℝ) :
    IsIntegralKernel (truncatedKernel r k) (hk.truncatedOperator r) :=
  isIntegralKernel_truncatedKernelOperator _ _ _

theorem IsIntegralKernel.norm_truncatedOperator_le
    [IsFiniteMeasure μ] [SFinite ν] (hk : IsIntegralKernel k K) (r : ℝ) :
    ‖hk.truncatedOperator r‖ ≤ ‖K‖ :=
  norm_truncatedKernelOperator_le _ _ (norm_nonneg K) r

end ThesisCommon
