import ThesisCommon.Analysis.LInfinityL1Pairing
import ThesisCommon.Analysis.LInfinityEssSup
import ThesisCommon.Analysis.ClopenOperatorMeasure
import ThesisCommon.Analysis.BoundedMeasureDensity
import ThesisCommon.Analysis.L1OperatorLattice

/-! Actual L-infinity representatives of the adjoint-at-one functional of
positive real L1 operators. The input measure is finite; the output measure
is arbitrary. Bounded Radon--Nikodym density and indicator density construct
the representative, rather than assuming an L1 dual representation theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

theorem operatorRectangleMeasure_le_opNorm_smul
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    operatorRectangleMeasure T hT MeasurableSet.univ ≤ ENNReal.ofReal ‖T‖ • μ := by
  apply Measure.le_iff.mpr
  intro A hA
  change measureOfDominatedContent _ _ _ _ _ A ≤ _
  rw [measureOfDominatedContent_apply _ _ _ _ _ hA]
  exact operatorRectangleContent_le T hT MeasurableSet.univ hA

theorem exists_positive_adjoint_one_density
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ ‖T‖) ∧
      ∀ A, ∀ hA : MeasurableSet A,
        (∫ x in A, g x ∂μ) = ∫ y, T (lOneIndicator μ A hA) y ∂ν := by
  obtain ⟨g, hgm, hgb, hgi, hrep⟩ := exists_bounded_density_of_le_smul
    (operatorRectangleMeasure T hT MeasurableSet.univ) μ (norm_nonneg T)
    (operatorRectangleMeasure_le_opNorm_smul T hT)
  refine ⟨g, hgm, hgb, fun A hA => ?_⟩
  have heq := congrArg (fun M : Measure X => M A) hrep
  dsimp only at heq
  rw [withDensity_apply _ hA, operatorRectangleMeasure_apply T hT MeasurableSet.univ hA,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
      (Eventually.of_forall fun x => (hgb x).1)] at heq
  have hgpos : 0 ≤ ∫ x in A, g x ∂μ := integral_nonneg fun x => (hgb x).1
  have hTpos : 0 ≤ ∫ y, T (lOneIndicator μ A hA) y ∂ν :=
    integral_nonneg_of_ae ((Lp.coeFn_nonneg _).mpr (hT _ (lOneIndicator_nonneg A hA)))
  simpa only [ENNReal.toReal_ofReal hgpos, ENNReal.toReal_ofReal hTpos] using
    congrArg ENNReal.toReal heq

def positiveAdjointOneDensity (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) : X → ℝ :=
  Classical.choose (exists_positive_adjoint_one_density T hT)

theorem measurable_positiveAdjointOneDensity
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    Measurable (positiveAdjointOneDensity T hT) :=
  (Classical.choose_spec (exists_positive_adjoint_one_density T hT)).1

theorem positiveAdjointOneDensity_bounds
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) (x : X) :
    0 ≤ positiveAdjointOneDensity T hT x ∧ positiveAdjointOneDensity T hT x ≤ ‖T‖ :=
  (Classical.choose_spec (exists_positive_adjoint_one_density T hT)).2.1 x

theorem positiveAdjointOneDensity_indicator
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) (A : Set X) (hA : MeasurableSet A) :
    (∫ x in A, positiveAdjointOneDensity T hT x ∂μ) =
      ∫ y, T (lOneIndicator μ A hA) y ∂ν :=
  (Classical.choose_spec (exists_positive_adjoint_one_density T hT)).2.2 A hA

theorem positiveAdjointOneDensity_memLp
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    MemLp (positiveAdjointOneDensity T hT) ∞ μ :=
  memLp_top_of_bound (measurable_positiveAdjointOneDensity T hT).aestronglyMeasurable ‖T‖
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (positiveAdjointOneDensity_bounds T hT x).1]
      exact (positiveAdjointOneDensity_bounds T hT x).2)

def positiveAdjointOne (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) : Lp ℝ ∞ μ :=
  (positiveAdjointOneDensity_memLp T hT).toLp (positiveAdjointOneDensity T hT)

theorem positiveAdjointOne_coe
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    positiveAdjointOne T hT =ᵐ[μ] positiveAdjointOneDensity T hT := MemLp.coeFn_toLp _

theorem positiveAdjointOne_nonneg
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) : 0 ≤ positiveAdjointOne T hT := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [positiveAdjointOne_coe T hT] with x hx
  change 0 ≤ positiveAdjointOne T hT x
  rw [hx]
  exact (positiveAdjointOneDensity_bounds T hT x).1

theorem norm_positiveAdjointOne_le
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) : ‖positiveAdjointOne T hT‖ ≤ ‖T‖ := by
  apply linfty_norm_le_of_ae_bound _ (norm_nonneg T)
  filter_upwards [positiveAdjointOne_coe T hT] with x hx
  rw [hx, Real.norm_of_nonneg (positiveAdjointOneDensity_bounds T hT x).1]
  exact (positiveAdjointOneDensity_bounds T hT x).2

theorem positiveAdjointOne_pairing
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    linftyL1Pairing μ (positiveAdjointOne T hT) =
      banachAdjoint T (linftyL1Pairing ν (linftyOne ν)) := by
  rw [linftyL1Pairing_one]
  apply lOne_continuousLinearMap_ext_indicators
  intro A hA
  rw [linftyL1Pairing_indicator]
  change (∫ x in A, positiveAdjointOne T hT x ∂μ) = L1.integralCLM (T (lOneIndicator μ A hA))
  rw [← L1.integral_def, L1.integral_eq_integral]
  exact (integral_congr_ae (ae_restrict_of_ae (positiveAdjointOne_coe T hT))).trans
    (positiveAdjointOneDensity_indicator T hT A hA)

theorem positiveAdjointOne_pairing_apply
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) (f : Lp ℝ 1 μ) :
    linftyL1Pairing μ (positiveAdjointOne T hT) f = ∫ y, T f y ∂ν := by
  rw [positiveAdjointOne_pairing, linftyL1Pairing_one]
  change L1.integralCLM (T f) = _
  rw [← L1.integral_def, L1.integral_eq_integral]

theorem lOne_norm_eq_integral_of_nonneg (f : Lp ℝ 1 ν) (hf : 0 ≤ f) :
    ‖f‖ = ∫ y, f y ∂ν := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with y hy
  exact Real.norm_of_nonneg hy

theorem norm_positiveAdjointOne
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) : ‖positiveAdjointOne T hT‖ = ‖T‖ := by
  apply le_antisymm (norm_positiveAdjointOne_le T hT)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have hdom : |T f| ≤ T |f| := by
    have h := lOneOperatorModulus_dominates T f
    rwa [← abs_lOneOperator_eq, abs_of_nonneg hT] at h
  calc
    ‖T f‖ ≤ ‖T |f|‖ := norm_le_norm_of_abs_le_abs (by
      rwa [abs_of_nonneg (hT |f| (abs_nonneg f))])
    _ = linftyL1Pairing μ (positiveAdjointOne T hT) |f| := by
      rw [lOne_norm_eq_integral_of_nonneg _ (hT |f| (abs_nonneg f)),
        positiveAdjointOne_pairing_apply]
    _ ≤ ‖linftyL1Pairing μ (positiveAdjointOne T hT) |f|‖ := le_abs_self _
    _ ≤ ‖positiveAdjointOne T hT‖ * ‖|f|‖ := linftyL1Pairing_bound _ _
    _ = _ := by rw [norm_abs_eq_norm]

theorem norm_eq_essSup_positiveAdjointOne
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    ‖T‖ = essSup (fun x => positiveAdjointOne T hT x) μ :=
  (norm_positiveAdjointOne T hT).symm.trans
    (linfty_norm_eq_essSup_of_nonneg _ (positiveAdjointOne_nonneg T hT))

theorem norm_eq_essSup_positiveAdjointOneDensity
    (T : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) :
    ‖T‖ = essSup (positiveAdjointOneDensity T hT) μ :=
  (norm_eq_essSup_positiveAdjointOne T hT).trans
    (essSup_congr_ae (positiveAdjointOne_coe T hT))

theorem positiveAdjointOne_add
    (T U : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν) (hT : 0 ≤ T) (hU : 0 ≤ U) :
    positiveAdjointOne (T + U) (add_nonneg hT hU) = positiveAdjointOne T hT + positiveAdjointOne U hU := by
  apply linftyL1Pairing_injective
  apply ContinuousLinearMap.ext
  intro f
  rw [map_add, ContinuousLinearMap.add_apply, positiveAdjointOne_pairing_apply,
    positiveAdjointOne_pairing_apply, positiveAdjointOne_pairing_apply]
  change (∫ y, (T f + U f) y ∂ν) = _
  rw [integral_congr_ae (Lp.coeFn_add (T f) (U f))]
  exact integral_add (L1.integrable_coeFn _) (L1.integrable_coeFn _)

end ThesisCommon
