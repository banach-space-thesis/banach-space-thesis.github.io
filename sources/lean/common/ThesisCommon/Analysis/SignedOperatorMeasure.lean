import ThesisCommon.Analysis.ClopenOperatorMeasureLattice
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Algebra.Order.Group.PosPart

/-! Signed product measures of real L1 operators. The positive and negative
operator parts give mutually singular finite measures, hence an actual Jordan
decomposition. The resulting signed measure is independent of positive
decomposition and has total variation equal to the measure of the modulus. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
variable [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
variable [SecondCountableTopology X] [SecondCountableTopology Y]
variable [BorelSpace X] [BorelSpace Y]

def operatorJordanDecomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    JordanDecomposition (X × Y) where
  posPart := clopenOperatorMeasure T⁺ (posPart_nonneg T)
  negPart := clopenOperatorMeasure T⁻ (negPart_nonneg T)
  mutuallySingular := (clopenOperatorMeasure_mutuallySingular_iff T⁺ T⁻
    (posPart_nonneg T) (negPart_nonneg T)).mpr (posPart_inf_negPart_eq_zero T)

def signedOperatorMeasure (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) : SignedMeasure (X × Y) :=
  (operatorJordanDecomposition T).toSignedMeasure

theorem signedOperatorMeasure_def (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    signedOperatorMeasure T =
      (clopenOperatorMeasure T⁺ (posPart_nonneg T)).toSignedMeasure -
      (clopenOperatorMeasure T⁻ (negPart_nonneg T)).toSignedMeasure := rfl

theorem signedOperatorMeasure_toJordanDecomposition (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    (signedOperatorMeasure T).toJordanDecomposition = operatorJordanDecomposition T :=
  JordanDecomposition.toJordanDecomposition_toSignedMeasure _

theorem signedOperatorMeasure_totalVariation (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    (signedOperatorMeasure T).totalVariation = clopenOperatorMeasure |T| (abs_nonneg T) := by
  rw [SignedMeasure.totalVariation, signedOperatorMeasure_toJordanDecomposition]
  change clopenOperatorMeasure T⁺ (posPart_nonneg T) +
    clopenOperatorMeasure T⁻ (negPart_nonneg T) = _
  simpa only [posPart_add_negPart] using
    (clopenOperatorMeasure_add T⁺ T⁻ (posPart_nonneg T) (negPart_nonneg T)).symm

omit [SigmaFinite ν] in
/-- The signed difference is independent of any chosen positive decomposition. -/
theorem clopenOperatorMeasure_signedDifference_eq
    (S T U V : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (h : S - T = U - V) :
    (clopenOperatorMeasure S hS).toSignedMeasure - (clopenOperatorMeasure T hT).toSignedMeasure =
      (clopenOperatorMeasure U hU).toSignedMeasure - (clopenOperatorMeasure V hV).toSignedMeasure := by
  have heq : S + V = U + T := sub_eq_sub_iff_add_eq_add.mp h
  have hm : clopenOperatorMeasure S hS + clopenOperatorMeasure V hV =
      clopenOperatorMeasure U hU + clopenOperatorMeasure T hT := by
    calc
      _ = clopenOperatorMeasure (S + V) (add_nonneg hS hV) :=
        (clopenOperatorMeasure_add S V hS hV).symm
      _ = clopenOperatorMeasure (U + T) (add_nonneg hU hT) := by simp only [heq]
      _ = _ := clopenOperatorMeasure_add U T hU hT
  have hsm := Measure.toSignedMeasure_congr hm
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at hsm
  exact sub_eq_sub_iff_add_eq_add.mpr hsm

theorem signedOperatorMeasure_sub_nonneg
    (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    signedOperatorMeasure (S - T) =
      (clopenOperatorMeasure S hS).toSignedMeasure - (clopenOperatorMeasure T hT).toSignedMeasure :=
  clopenOperatorMeasure_signedDifference_eq (S - T)⁺ (S - T)⁻ S T
    (posPart_nonneg _) (negPart_nonneg _) hS hT (posPart_sub_negPart _)

theorem signedOperatorMeasure_nonneg
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    signedOperatorMeasure S = (clopenOperatorMeasure S hS).toSignedMeasure := by
  have h := signedOperatorMeasure_sub_nonneg S 0 hS le_rfl
  simpa only [sub_zero, clopenOperatorMeasure_zero, Measure.toSignedMeasure_zero] using h

theorem signedOperatorMeasure_zero :
    signedOperatorMeasure (0 : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) = 0 := by
  simp only [signedOperatorMeasure_nonneg 0 le_rfl, clopenOperatorMeasure_zero,
    Measure.toSignedMeasure_zero]

theorem signedOperatorMeasure_add (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    signedOperatorMeasure (S + T) = signedOperatorMeasure S + signedOperatorMeasure T := by
  have heq : S + T = (S⁺ + T⁺) - (S⁻ + T⁻) := by
    rw [add_sub_add_comm, posPart_sub_negPart, posPart_sub_negPart]
  rw [heq, signedOperatorMeasure_sub_nonneg _ _
    (add_nonneg (posPart_nonneg S) (posPart_nonneg T))
    (add_nonneg (negPart_nonneg S) (negPart_nonneg T))]
  have hp := Measure.toSignedMeasure_congr
    (clopenOperatorMeasure_add S⁺ T⁺ (posPart_nonneg S) (posPart_nonneg T))
  have hn := Measure.toSignedMeasure_congr
    (clopenOperatorMeasure_add S⁻ T⁻ (negPart_nonneg S) (negPart_nonneg T))
  rw [Measure.toSignedMeasure_add] at hp hn
  rw [hp, hn, signedOperatorMeasure_def, signedOperatorMeasure_def]
  exact add_sub_add_comm _ _ _ _

theorem signedOperatorMeasure_neg (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    signedOperatorMeasure (-T) = -signedOperatorMeasure T := by
  have h := signedOperatorMeasure_add T (-T)
  rw [add_neg_cancel, signedOperatorMeasure_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem signedOperatorMeasure_sub (S T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    signedOperatorMeasure (S - T) = signedOperatorMeasure S - signedOperatorMeasure T := by
  rw [sub_eq_add_neg, signedOperatorMeasure_add, signedOperatorMeasure_neg, sub_eq_add_neg]

theorem signedOperatorMeasure_rectangle (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν)
    (a : Set X) (ha : MeasurableSet a) (b : Set Y) (hb : MeasurableSet b) :
    signedOperatorMeasure T (a ×ˢ b) = ∫ y in b, T (lOneIndicator μ a ha) y ∂ν := by
  rw [signedOperatorMeasure_def, Measure.toSignedMeasure_sub_apply (ha.prod hb)]
  simp only [Measure.real, clopenOperatorMeasure_prod _ _ ha hb]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae
    ((Lp.coeFn_nonneg _).mpr (posPart_nonneg T _ (lOneIndicator_nonneg a ha))))),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae
      ((Lp.coeFn_nonneg _).mpr (negPart_nonneg T _ (lOneIndicator_nonneg a ha)))))]
  rw [← integral_sub (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn]
  have hop : T⁺ (lOneIndicator μ a ha) - T⁻ (lOneIndicator μ a ha) =
      T (lOneIndicator μ a ha) := DFunLike.congr_fun (posPart_sub_negPart T) _
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (μ := ν) (s := b)
    (Lp.coeFn_sub (T⁺ (lOneIndicator μ a ha)) (T⁻ (lOneIndicator μ a ha)))] with y hy
  rw [hop] at hy
  exact hy.symm

omit [SigmaFinite ν] in
theorem clopenOperatorMeasure_nnreal_smul (c : ℝ≥0)
    (S : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hS : 0 ≤ S) :
    clopenOperatorMeasure ((c : ℝ) • S) (smul_nonneg c.property hS) =
      c • clopenOperatorMeasure S hS := by
  apply Measure.ext_prod
  intro a b ha hb
  rw [clopenOperatorMeasure_prod _ _ ha hb, Measure.smul_apply,
    clopenOperatorMeasure_prod _ _ ha hb]
  change ENNReal.ofReal (∫ y in b, ((c : ℝ) • S (lOneIndicator μ a ha)) y ∂ν) = _
  rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul (c : ℝ) (S (lOneIndicator μ a ha))))]
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul]
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul] using
    (ENNReal.ofReal_mul (p := (c : ℝ))
      (q := ∫ y in b, S (lOneIndicator μ a ha) y ∂ν) c.property)

theorem signedOperatorMeasure_smul_nonneg (c : ℝ) (hc : 0 ≤ c)
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    signedOperatorMeasure (c • T) = c • signedOperatorMeasure T := by
  lift c to ℝ≥0 using hc
  have heq : (c : ℝ) • T = (c : ℝ) • T⁺ - (c : ℝ) • T⁻ := by
    rw [← smul_sub, posPart_sub_negPart]
  have hP : 0 ≤ (c : ℝ) • T⁺ := smul_nonneg c.property (posPart_nonneg T)
  have hN : 0 ≤ (c : ℝ) • T⁻ := smul_nonneg c.property (negPart_nonneg T)
  calc
    signedOperatorMeasure ((c : ℝ) • T) =
        signedOperatorMeasure ((c : ℝ) • T⁺ - (c : ℝ) • T⁻) := congrArg _ heq
    _ = (clopenOperatorMeasure ((c : ℝ) • T⁺) hP).toSignedMeasure -
        (clopenOperatorMeasure ((c : ℝ) • T⁻) hN).toSignedMeasure :=
      signedOperatorMeasure_sub_nonneg ((c : ℝ) • T⁺) ((c : ℝ) • T⁻) hP hN
    _ = (c : ℝ) • signedOperatorMeasure T := ?_
  have hp := Measure.toSignedMeasure_congr
    (clopenOperatorMeasure_nnreal_smul c T⁺ (posPart_nonneg T))
  have hn := Measure.toSignedMeasure_congr
    (clopenOperatorMeasure_nnreal_smul c T⁻ (negPart_nonneg T))
  rw [Measure.toSignedMeasure_smul] at hp hn
  rw [hp, hn, signedOperatorMeasure_def, smul_sub]
  rfl

theorem signedOperatorMeasure_smul (c : ℝ) (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    signedOperatorMeasure (c • T) = c • signedOperatorMeasure T := by
  by_cases hc : 0 ≤ c
  · exact signedOperatorMeasure_smul_nonneg c hc T
  · have hc' : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
    have h := signedOperatorMeasure_smul_nonneg (-c) hc' T
    rw [neg_smul, signedOperatorMeasure_neg, neg_smul] at h
    exact neg_injective h

def signedOperatorMeasureLinear :
    (Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) →ₗ[ℝ] SignedMeasure (X × Y) where
  toFun := signedOperatorMeasure
  map_add' := signedOperatorMeasure_add
  map_smul' := signedOperatorMeasure_smul

theorem signedOperatorMeasure_injective :
    Function.Injective (signedOperatorMeasure (μ := μ) (ν := ν)) := by
  intro S T hST
  apply lOne_continuousLinearMap_ext_indicators
  intro a ha
  apply lOne_eq_of_setIntegrals_eq
  intro b hb _
  have h := congrArg (fun M : SignedMeasure (X × Y) => M (a ×ˢ b)) hST
  simpa only [signedOperatorMeasure_rectangle _ a ha b hb] using h

theorem signedOperatorMeasure_totalVariation_fst_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    (signedOperatorMeasure T).totalVariation.fst ≤ ENNReal.ofReal ‖T‖ • μ := by
  rw [signedOperatorMeasure_totalVariation]
  simpa only [norm_abs_lOneOperator] using clopenOperatorMeasure_fst_le |T| (abs_nonneg T)

theorem signedOperatorMeasure_totalVariation_snd_absolutelyContinuous
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) :
    (signedOperatorMeasure T).totalVariation.snd ≪ ν := by
  rw [signedOperatorMeasure_totalVariation]
  exact clopenOperatorMeasure_snd_absolutelyContinuous |T| (abs_nonneg T)

end ThesisCommon
