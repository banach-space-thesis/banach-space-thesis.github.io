import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/-! The measure-extension step for a positive content dominated by a finite
measure. Domination makes continuity at the empty set automatic. This expands
the extension step in the proof that integral operators form an order ideal. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {X : Type*} [mX : MeasurableSpace X] {C : Set (Set X)}

theorem content_sigmaSubadditive_of_le_finiteMeasure
    (hC : IsSetRing C) (hmeas : ∀ s ∈ C, MeasurableSet s)
    (c : AddContent C) (ρ : Measure X) [IsFiniteMeasure ρ]
    (hdom : ∀ s ∈ C, c s ≤ ρ s) : c.IsSigmaSubadditive := by
  apply isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC
  intro f hf hUf hdisj
  apply addContent_iUnion_eq_sum_of_tendsto_zero hC c
    (fun s hs => ne_top_of_le_ne_top (measure_ne_top ρ s) (hdom s hs)) _ hf hUf hdisj
  intro s hs hanti hinter
  have hlim : Tendsto (fun n => ρ (s n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hinter, measure_empty] using
      tendsto_measure_iInter_atTop (fun n => (hmeas _ (hs n)).nullMeasurableSet) hanti
        ⟨0, measure_ne_top ρ (s 0)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun n => hdom _ (hs n))

/-- Caratheodory extension of a dominated content on a generating algebra.
Its values are proved below, rather than stipulated as structure fields. -/
def measureOfDominatedContent (hC : IsSetAlgebra C)
    (hgen : mX = MeasurableSpace.generateFrom C) (c : AddContent C)
    (ρ : Measure X) [IsFiniteMeasure ρ] (hdom : ∀ s ∈ C, c s ≤ ρ s) : Measure X :=
  c.measure hC.isSetRing.isSetSemiring hgen.le
    (content_sigmaSubadditive_of_le_finiteMeasure hC.isSetRing
      (fun _ hs => hgen ▸ MeasurableSpace.measurableSet_generateFrom hs) c ρ hdom)

theorem measureOfDominatedContent_apply (hC : IsSetAlgebra C)
    (hgen : mX = MeasurableSpace.generateFrom C) (c : AddContent C)
    (ρ : Measure X) [IsFiniteMeasure ρ] (hdom : ∀ s ∈ C, c s ≤ ρ s)
    {s : Set X} (hs : s ∈ C) : measureOfDominatedContent hC hgen c ρ hdom s = c s :=
  c.measure_eq hC.isSetRing.isSetSemiring hgen _ hs

instance isFiniteMeasure_measureOfDominatedContent (hC : IsSetAlgebra C)
    (hgen : mX = MeasurableSpace.generateFrom C) (c : AddContent C)
    (ρ : Measure X) [IsFiniteMeasure ρ] (hdom : ∀ s ∈ C, c s ≤ ρ s) :
    IsFiniteMeasure (measureOfDominatedContent hC hgen c ρ hdom) where
  measure_univ_lt_top := by
    rw [measureOfDominatedContent_apply hC hgen c ρ hdom hC.univ_mem]
    exact (hdom _ hC.univ_mem).trans_lt (measure_lt_top ρ univ)

end ThesisCommon
