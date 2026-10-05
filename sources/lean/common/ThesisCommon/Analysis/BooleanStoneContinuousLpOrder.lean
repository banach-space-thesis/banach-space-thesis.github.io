import ThesisCommon.Analysis.BooleanStoneContinuousLp
import Mathlib.MeasureTheory.Function.LpOrder

/-! Positivity reflection for the actual real Stone continuous/L∞
representation, from positivity of every nonempty Stone clopen. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {B : Type*} [BooleanAlgebra B]
variable (μ : Measure (BooleanStonePoint B)) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem booleanStone_continuous_nonneg_of_ae
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (f : C(BooleanStonePoint B, ℝ)) (hf : ∀ᵐ p ∂μ, 0 ≤ f p) : 0 ≤ f := by
  intro p
  by_contra hp
  have hlt : f p < 0 := lt_of_not_ge hp
  have hU : IsOpen {q : BooleanStonePoint B | f q < 0} :=
    isOpen_lt f.continuous continuous_const
  obtain ⟨U, ⟨a, rfl⟩, hpa, ha⟩ :=
    isTopologicalBasis_range_booleanStoneSet.mem_nhds_iff.mp (hU.mem_nhds hlt)
  have hpos := hμ a ((booleanStoneSet_nonempty_iff a).mp ⟨p, hpa⟩)
  have hz : μ (booleanStoneSet a) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hf] with q hq
    exact fun hqa => (not_lt_of_ge hq) (ha hqa)
  exact (ne_of_gt hpos) hz

theorem booleanStoneContinuousLInfinityEquiv_nonneg
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (hrep : ∀ A : Set (BooleanStonePoint B), MeasurableSet A →
      ∃ a : B, A =ᵐ[μ] booleanStoneSet a)
    (f : C(BooleanStonePoint B, ℝ)) :
    0 ≤ booleanStoneContinuousLInfinityEquiv (𝕜 := ℝ) μ hμ hrep f ↔ 0 ≤ f := by
  have hcoe : booleanStoneContinuousLInfinityEquiv (𝕜 := ℝ) μ hμ hrep f =ᵐ[μ] f :=
    booleanStoneContinuousLInfinityIsometry_coe μ hμ f
  constructor
  · intro h
    apply booleanStone_continuous_nonneg_of_ae μ hμ f
    filter_upwards [(Lp.coeFn_nonneg _).mpr h, hcoe] with p hp heq
    rwa [heq] at hp
  · intro h
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hcoe] with p hp
    rw [hp]
    exact h p

end ThesisCommon
