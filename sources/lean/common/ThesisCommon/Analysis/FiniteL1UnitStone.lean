import ThesisCommon.Analysis.ALPrincipalL1Representation
import ThesisCommon.Analysis.ALDedekindComplete
import ThesisCommon.Analysis.ALFragmentCompleteBoolean
import ThesisCommon.Analysis.L1Lattice

/-! The fragments of the constant one function give a finite Stone model
of an arbitrary finite-measure real L1 space. The model preserves one. -/
noncomputable section
open Set MeasureTheory Filter
namespace ThesisCommon
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

abbrev lOneUnit : Lp ℝ 1 μ := lOneIndicator μ univ MeasurableSet.univ

instance lOneUnit_nonneg : Fact (0 ≤ lOneUnit μ) := ⟨lOneIndicator_nonneg _ _⟩

abbrev L1UnitFragments := PositiveFragmentAlgebra (lOneUnit μ)

instance lOneUnitFragments_completeBoolean : CompleteBooleanAlgebra (L1UnitFragments μ) :=
  positiveFragmentCompleteBoolean (lOne_norm_add_of_nonneg μ) (lOneUnit μ)

abbrev L1UnitStone := BooleanStonePoint (L1UnitFragments μ)

def lOneUnitStoneMeasure : Measure (L1UnitStone μ) :=
  alFragmentMeasure (lOne_norm_add_of_nonneg μ) (lOneUnit μ)

instance lOneUnitStoneMeasure_finite : IsFiniteMeasure (lOneUnitStoneMeasure μ) :=
  inferInstanceAs (IsFiniteMeasure (alFragmentMeasure (lOne_norm_add_of_nonneg μ) (lOneUnit μ)))

theorem lOneIndicator_isPositiveFragment (s : Set X) (hs : MeasurableSet s) :
    IsPositiveFragment (lOneIndicator μ s hs) (lOneUnit μ) := by
  refine ⟨lOneIndicator_nonneg _ _, ?_, ?_⟩
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [lOneIndicator_coe (μ := μ) s hs,
      lOneIndicator_coe (μ := μ) univ MeasurableSet.univ] with x hx ho
    rw [hx, ho]
    by_cases h : x ∈ s <;> simp [h]
  · apply Lp.ext
    filter_upwards [Lp.coeFn_inf (lOneIndicator μ s hs) (lOneUnit μ-lOneIndicator μ s hs),
      Lp.coeFn_sub (lOneUnit μ) (lOneIndicator μ s hs), Lp.coeFn_zero (E := ℝ) (p := 1) μ,
      lOneIndicator_coe (μ := μ) s hs,
      lOneIndicator_coe (μ := μ) univ MeasurableSet.univ] with x hi hsub hz hx ho
    rw [hi, hz]
    change min (lOneIndicator μ s hs x) ((lOneUnit μ-lOneIndicator μ s hs) x) = 0
    rw [hsub]
    change min (lOneIndicator μ s hs x) (lOneUnit μ x-lOneIndicator μ s hs x) = 0
    rw [hx, ho]
    by_cases h : x ∈ s <;> simp [h]

local instance finiteUnitStoneL1ConditionalLattice : ConditionallyCompleteLattice (Lp ℝ 1 μ) :=
  alConditionallyCompleteLattice (lOne_norm_add_of_nonneg μ)

def lOneUnitStoneMap : Lp ℝ 1 (lOneUnitStoneMeasure μ) →L[ℝ] Lp ℝ 1 μ :=
  alFragmentL1Map (lOne_norm_add_of_nonneg μ) (lOneUnit μ)

theorem lOneUnitStoneMap_norm (f : Lp ℝ 1 (lOneUnitStoneMeasure μ)) :
    ‖lOneUnitStoneMap μ f‖ = ‖f‖ :=
  alFragmentL1Map_norm (lOne_norm_add_of_nonneg μ) (lOneUnit μ) f

theorem lOneUnitStoneMap_surjective : Function.Surjective (lOneUnitStoneMap μ) := by
  intro f
  let S := LinearMap.range (lOneUnitStoneMap μ).toLinearMap
  have hS : IsClosed (S : Set (Lp ℝ 1 μ)) :=
    (alFragmentL1Isometry (lOne_norm_add_of_nonneg μ) (lOneUnit μ)).isometry.isClosedEmbedding.isClosed_range
  have hf : f ∈ S := by
    apply Lp.induction (p := 1) (by norm_num) (fun g => g ∈ S)
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_smul_lOneIndicator]
      apply S.smul_mem
      exact ⟨alFragmentIndicator (lOne_norm_add_of_nonneg μ) (lOneUnit μ)
        (positiveFragmentOf (lOneIndicator_isPositiveFragment μ s hs)),
        alFragmentL1Map_fragment (lOne_norm_add_of_nonneg μ) (lOneUnit μ) _⟩
    · intro g h hg hh _ hgs hhs
      exact S.add_mem hgs hhs
    · exact hS
  exact hf

def lOneUnitStoneEquiv : Lp ℝ 1 (lOneUnitStoneMeasure μ) ≃ₗᵢ[ℝ] Lp ℝ 1 μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (lOneUnitStoneMap μ).toLinearMap, norm_map' := lOneUnitStoneMap_norm μ }
    (lOneUnitStoneMap_surjective μ)

theorem lOneUnitStoneEquiv_nonneg (f : Lp ℝ 1 (lOneUnitStoneMeasure μ)) :
    0 ≤ lOneUnitStoneEquiv μ f ↔ 0 ≤ f :=
  alFragmentL1Map_nonneg_iff (lOne_norm_add_of_nonneg μ) (lOneUnit μ) f

theorem lOneUnitStoneEquiv_one :
    lOneUnitStoneEquiv μ (lOneUnit (lOneUnitStoneMeasure μ)) = lOneUnit μ := by
  change alFragmentL1Map (lOne_norm_add_of_nonneg μ) (lOneUnit μ)
    (lOneIndicator _ univ MeasurableSet.univ) = lOneUnit μ
  have h := alFragmentL1Map_fragment (lOne_norm_add_of_nonneg μ) (lOneUnit μ) ⊤
  simpa only [alFragmentIndicator_eq_lOneIndicator, booleanStoneSet_top, positiveFragmentValue_top]
    using h

end ThesisCommon
