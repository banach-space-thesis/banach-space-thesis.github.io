import ThesisCommon.Analysis.KernelProductRestriction
import ThesisCommon.Analysis.SignedOperatorMeasure
import ThesisCommon.Analysis.KernelOperatorNorm

/-! Measurable signed reverse kernels with genuine fibrewise Jordan
decompositions. A global Hahn set splits a bounded disintegration of the
total variation, so the exact fibre variation and its bound hold everywhere. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

structure SignedReverseKernel (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  posPart : Kernel X Y
  negPart : Kernel X Y
  [posPart_finite : IsFiniteKernel posPart]
  [negPart_finite : IsFiniteKernel negPart]
  mutuallySingular : ∀ x, posPart x ⟂ₘ negPart x

attribute [instance] SignedReverseKernel.posPart_finite SignedReverseKernel.negPart_finite

namespace SignedReverseKernel

def jordan (K : SignedReverseKernel X Y) (x : X) : JordanDecomposition Y where
  posPart := K.posPart x
  negPart := K.negPart x
  mutuallySingular := K.mutuallySingular x

def fibre (K : SignedReverseKernel X Y) (x : X) : SignedMeasure Y := (K.jordan x).toSignedMeasure

def variationKernel (K : SignedReverseKernel X Y) : Kernel X Y := K.posPart + K.negPart

instance variationKernel_finite (K : SignedReverseKernel X Y) : IsFiniteKernel K.variationKernel := by
  unfold variationKernel
  infer_instance

theorem fibre_totalVariation (K : SignedReverseKernel X Y) (x : X) :
    (K.fibre x).totalVariation = K.variationKernel x := by
  rw [fibre, SignedMeasure.totalVariation, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  rfl

theorem fibre_measurable (K : SignedReverseKernel X Y) (b : Set Y) (hb : MeasurableSet b) :
    Measurable (fun x => K.fibre x b) := by
  have h : (fun x => K.fibre x b) =
      fun x => (K.posPart x b).toReal - (K.negPart x b).toReal := by
    funext x
    exact Measure.toSignedMeasure_sub_apply hb
  rw [h]
  exact (Kernel.measurable_coe _ hb).ennreal_toReal.sub (Kernel.measurable_coe _ hb).ennreal_toReal

def ofSplit (κ : Kernel X Y) [IsFiniteKernel κ] (s : Set (X × Y))
    (hs : MeasurableSet s) : SignedReverseKernel X Y where
  posPart := productSetKernel κ s
  negPart := productSetKernel κ sᶜ
  mutuallySingular := productSetKernel_mutuallySingular κ s hs

theorem ofSplit_variationKernel (κ : Kernel X Y) [IsFiniteKernel κ]
    (s : Set (X × Y)) (hs : MeasurableSet s) : (ofSplit κ s hs).variationKernel = κ := by
  ext1 x
  exact productSetKernel_add_compl κ s hs x

end SignedReverseKernel

/-- Disintegration of a genuine finite Jordan pair. The two kernel parts
are mutually singular at every input point, including null exceptional inputs. -/
theorem exists_bounded_signedReverseKernel (μ : Measure X) [IsFiniteMeasure μ]
    [StandardBorelSpace Y] (j : JordanDecomposition (X × Y)) (C : ℝ) (hC : 0 ≤ C)
    (hfst : (j.posPart + j.negPart).fst ≤ ENNReal.ofReal C • μ) :
    ∃ K : SignedReverseKernel X Y,
      (∀ x, K.variationKernel x univ ≤ ENNReal.ofReal C) ∧
      μ ⊗ₘ K.posPart = j.posPart ∧ μ ⊗ₘ K.negPart = j.negPart := by
  obtain ⟨κ, hκ, hmass, hrepr⟩ :=
    exists_bounded_disintegration μ (j.posPart + j.negPart) hC hfst
  letI := hκ
  obtain ⟨s, hs, hP, hN⟩ := j.mutuallySingular
  have hPc : j.posPart.restrict sᶜ = j.posPart := by
    have h := Measure.restrict_add_restrict_compl (μ := j.posPart) hs
    rw [Measure.restrict_eq_zero.mpr hP, zero_add] at h
    exact h
  have hNs : j.negPart.restrict s = j.negPart := by
    have h := Measure.restrict_add_restrict_compl (μ := j.negPart) hs
    rw [Measure.restrict_eq_zero.mpr hN, add_zero] at h
    exact h
  refine ⟨SignedReverseKernel.ofSplit κ sᶜ hs.compl, ?_, ?_, ?_⟩
  · simpa only [SignedReverseKernel.ofSplit_variationKernel] using hmass
  · change μ ⊗ₘ productSetKernel κ sᶜ = j.posPart
    rw [compProd_productSetKernel μ κ sᶜ hs.compl, hrepr, Measure.restrict_add,
      hPc, Measure.restrict_eq_zero.mpr hN, add_zero]
  · change μ ⊗ₘ productSetKernel κ sᶜᶜ = j.negPart
    rw [compl_compl, compProd_productSetKernel μ κ s hs, hrepr, Measure.restrict_add,
      Measure.restrict_eq_zero.mpr hP, zero_add, hNs]

theorem SignedReverseKernel.compProd_variationKernel (μ : Measure X) [SFinite μ]
    (K : SignedReverseKernel X Y) :
    μ ⊗ₘ K.variationKernel = μ ⊗ₘ K.posPart + μ ⊗ₘ K.negPart := by
  rw [SignedReverseKernel.variationKernel, Measure.compProd_add_right]

variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

theorem exists_signedOperatorReverseKernel [StandardBorelSpace Y]
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    ∃ K : SignedReverseKernel X Y,
      (∀ x, (K.fibre x).totalVariation univ ≤ ENNReal.ofReal ‖T‖) ∧
      μ ⊗ₘ K.posPart = clopenOperatorMeasure T⁺ (posPart_nonneg T) ∧
      μ ⊗ₘ K.negPart = clopenOperatorMeasure T⁻ (negPart_nonneg T) ∧
      μ ⊗ₘ K.variationKernel = clopenOperatorMeasure |T| (abs_nonneg T) := by
  have hfst : ((operatorJordanDecomposition T).posPart +
      (operatorJordanDecomposition T).negPart).fst ≤ ENNReal.ofReal ‖T‖ • μ := by
    rw [← signedOperatorMeasure_toJordanDecomposition, ← SignedMeasure.totalVariation]
    exact signedOperatorMeasure_totalVariation_fst_le T
  obtain ⟨K, hmass, hP, hN⟩ := exists_bounded_signedReverseKernel μ
    (operatorJordanDecomposition T) ‖T‖ (norm_nonneg T) hfst
  refine ⟨K, ?_, hP, hN, ?_⟩
  · intro x
    rw [K.fibre_totalVariation]
    exact hmass x
  · rw [K.compProd_variationKernel μ, hP, hN]
    change clopenOperatorMeasure T⁺ (posPart_nonneg T) +
      clopenOperatorMeasure T⁻ (negPart_nonneg T) = _
    simpa only [posPart_add_negPart] using
      (clopenOperatorMeasure_add T⁺ T⁻ (posPart_nonneg T) (negPart_nonneg T)).symm

theorem signedOperator_norm_le_iff_reverseKernel_variation
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (K : SignedReverseKernel X Y)
    (hrepr : μ ⊗ₘ K.variationKernel = clopenOperatorMeasure |T| (abs_nonneg T))
    (C : ℝ) (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔ ∀ᵐ x ∂μ, (K.fibre x).totalVariation univ ≤ ENNReal.ofReal C := by
  simp only [K.fibre_totalVariation]
  rw [← norm_abs_lOneOperator T]
  exact positive_operator_norm_le_iff_kernel_mass |T| (abs_nonneg T) K.variationKernel hrepr C hC

end ThesisCommon
