import ThesisCommon.Analysis.ClopenOperatorMeasureLattice
import ThesisCommon.Analysis.KernelProductRestriction
import ThesisCommon.LpCut
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Exact operator norm tests from the fibre masses of a positive reverse
kernel. The norm bound is equivalent to an almost-everywhere fibre bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem compProd_fst_le_smul_iff (μ : Measure X) [SigmaFinite μ]
    (κ : Kernel X Y) [IsSFiniteKernel κ] (c : ℝ≥0∞) :
    (μ ⊗ₘ κ).fst ≤ c • μ ↔ ∀ᵐ x ∂μ, κ x univ ≤ c := by
  constructor
  · intro h
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Kernel.measurable_coe κ MeasurableSet.univ)
    intro a ha _
    have h' := h a
    rw [Measure.fst_apply ha, ← prod_univ,
      Measure.compProd_apply_prod ha MeasurableSet.univ] at h'
    simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul] using h'
  · intro h
    apply Measure.le_iff.mpr
    intro a ha
    rw [Measure.fst_apply ha, ← prod_univ, Measure.compProd_apply_prod ha MeasurableSet.univ,
      Measure.smul_apply, smul_eq_mul]
    calc
      (∫⁻ x in a, κ x univ ∂μ) ≤ ∫⁻ _x in a, c ∂μ :=
        lintegral_mono_ae (ae_restrict_of_ae h)
      _ = c * μ a := by simp

variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

theorem clopenOperatorMeasure_fst_le_iff_norm_le
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (C : ℝ) (hC : 0 ≤ C) :
    (clopenOperatorMeasure S hS).fst ≤ ENNReal.ofReal C • μ ↔ ‖S‖ ≤ C := by
  constructor
  · intro hfst
    let ρ := clopenOperatorMeasure S hS
    have hsnd : ρ.snd ≪ ν := clopenOperatorMeasure_snd_absolutelyContinuous S hS
    let U := operatorOfProductMeasure μ ν ρ C hC hfst hsnd
    have hU : 0 ≤ U := fun _ hf => operatorOfProductMeasure_nonneg μ ν ρ C hC hfst hsnd hf
    have heq : U = S := clopenOperatorMeasure_injective U S hU hS
      (clopenOperatorMeasure_operatorOfProductMeasure ρ C hC hfst hsnd)
    rw [← heq]
    exact operatorOfProductMeasure_norm_le μ ν ρ C hC hfst hsnd
  · intro hnorm
    apply (clopenOperatorMeasure_fst_le S hS).trans
    intro a
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hnorm) (μ a)

theorem positive_operator_norm_le_iff_kernel_mass
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ] (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (C : ℝ) (hC : 0 ≤ C) :
    ‖S‖ ≤ C ↔ ∀ᵐ x ∂μ, κ x univ ≤ ENNReal.ofReal C := by
  rw [← clopenOperatorMeasure_fst_le_iff_norm_le S hS C hC, ← hrepr,
    compProd_fst_le_smul_iff]

omit [IsFiniteMeasure μ] [SigmaFinite ν] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [BorelSpace X] [BorelSpace Y] in
theorem lOneCut_nonneg (b : Set Y) (hb : MeasurableSet b)
    {f : Lp ℝ 1 ν} (hf : 0 ≤ f) : 0 ≤ lpCut b hb f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [lpCut_coe b hb f, (Lp.coeFn_nonneg f).mpr hf] with y hy hn
  rw [hy]
  exact indicator_nonneg (fun _ _ => hn) y

omit [SigmaFinite ν] in
theorem clopenOperatorMeasure_outputCut
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (b : Set Y) (hb : MeasurableSet b) :
    clopenOperatorMeasure ((lpCutL b hb).comp S)
      (fun f hf => lOneCut_nonneg b hb (hS f hf)) =
      (clopenOperatorMeasure S hS).restrict (univ ×ˢ b) := by
  apply Measure.ext_prod
  intro a c ha hc
  rw [clopenOperatorMeasure_prod _ _ ha hc, Measure.restrict_apply (ha.prod hc),
    prod_inter_prod, inter_univ, clopenOperatorMeasure_prod _ _ ha (hc.inter hb)]
  change ENNReal.ofReal (∫ y in c, lpCut b hb (S (lOneIndicator μ a ha)) y ∂ν) = _
  rw [integral_congr_ae (ae_restrict_of_ae (lpCut_coe b hb (S (lOneIndicator μ a ha)))),
    setIntegral_indicator hb]

theorem positive_operator_outputCut_norm_le_iff_kernel_mass
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ] (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (b : Set Y) (hb : MeasurableSet b) (C : ℝ) (hC : 0 ≤ C) :
    ‖(lpCutL b hb).comp S‖ ≤ C ↔ ∀ᵐ x ∂μ, κ x b ≤ ENNReal.ofReal C := by
  have hpos : 0 ≤ (lpCutL b hb).comp S := fun f hf => lOneCut_nonneg b hb (hS f hf)
  have hreprCut : μ ⊗ₘ productSetKernel κ (univ ×ˢ b) =
      clopenOperatorMeasure ((lpCutL b hb).comp S) hpos := by
    rw [compProd_productSetKernel μ κ _ (MeasurableSet.univ.prod hb), hrepr,
      clopenOperatorMeasure_outputCut S hS b hb]
  rw [positive_operator_norm_le_iff_kernel_mass _ hpos _ hreprCut C hC]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall fun x => by
    rw [productSetKernel_apply κ _ (MeasurableSet.univ.prod hb)]
    have hpre : Prod.mk x ⁻¹' ((univ : Set X) ×ˢ b) = b := by ext y; simp
    rw [hpre, Measure.restrict_apply_univ]

theorem positive_operator_outputCut_norm_le_iff_kernel_real_mass
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S)
    (κ : Kernel X Y) [IsFiniteKernel κ] (hrepr : μ ⊗ₘ κ = clopenOperatorMeasure S hS)
    (b : Set Y) (hb : MeasurableSet b) (C : ℝ) (hC : 0 ≤ C) :
    ‖(lpCutL b hb).comp S‖ ≤ C ↔ ∀ᵐ x ∂μ, (κ x).real b ≤ C := by
  rw [positive_operator_outputCut_norm_le_iff_kernel_mass S hS κ hrepr b hb C hC]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall fun x => by
    exact ENNReal.le_ofReal_iff_toReal_le (measure_ne_top (κ x) b) hC

end ThesisCommon
