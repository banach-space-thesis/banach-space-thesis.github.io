import ThesisCommon.Analysis.MeasureAlgebraMap
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Compactness.Compact

/-! Standard-space representation of a countably generated finite measure
algebra (PEMS Theorem 3.7). The countable generating sequence codes points
into Cantor space. Pullback of the pushforward measure is an isomorphism of
measure algebras even when the original sigma algebra does not separate points.
This supplies an explicit proof of the background representation theorem. -/
noncomputable section
open MeasureTheory MeasurableSpace Set
namespace ThesisCommon

/-- A standard measure space in the paper's convention: a finite Borel measure
on a compact metric space. Its carrier need not be the unit interval. -/
structure StandardFiniteMeasureSpace where
  carrier : Type
  [metric : MetricSpace carrier]
  [compact : CompactSpace carrier]
  [measurable : MeasurableSpace carrier]
  [borel : BorelSpace carrier]
  measure : Measure carrier
  [finite : IsFiniteMeasure measure]

attribute [instance] StandardFiniteMeasureSpace.metric StandardFiniteMeasureSpace.compact
  StandardFiniteMeasureSpace.measurable StandardFiniteMeasureSpace.borel
  StandardFiniteMeasureSpace.finite

variable (X : Type*) [mX : MeasurableSpace X] [CountablyGenerated X]

/-- The canonical Cantor coding generates exactly the original sigma algebra.
No assumption that measurable sets separate points appears here. -/
theorem comap_mapNatBool :
    (inferInstance : MeasurableSpace (ℕ → Bool)).comap (mapNatBool X) = mX := by
  apply le_antisymm (measurable_mapNatBool X).comap_le
  conv_lhs => rw [← generateFrom_natGeneratingSequence X]
  apply generateFrom_le
  rintro _ ⟨n, rfl⟩
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨{y : ℕ → Bool | y n = true}, by measurability, ?_⟩
  ext x
  simp [mapNatBool]

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The actual representing finite measure on the compact Cantor space. -/
def cantorMeasureModel (X : Type*) [MeasurableSpace X] [CountablyGenerated X]
    (μ : Measure X) [IsFiniteMeasure μ] : StandardFiniteMeasureSpace := by
  letI : MetricSpace (ℕ → Bool) := PiNat.metricSpace (E := fun _ => Bool)
  exact { carrier := ℕ → Bool, measure := μ.map (mapNatBool X) }

/-- Explicit, measure-preserving isomorphism from the original measure algebra
to that of its standard Cantor representation. -/
def cantorMeasureAlgebraIso : MeasureAlgebraIso μ (cantorMeasureModel X μ).measure :=
  (MeasureAlgebraIso.ofComapEq μ (mapNatBool X) (measurable_mapNatBool X)
    (comap_mapNatBool X)).symm

/-- Every countably generated finite measure space has a standard finite
measure-space representation, including atoms, null spaces and nonseparated
underlying measurable spaces. -/
theorem exists_standardFiniteMeasureSpace :
    ∃ S : StandardFiniteMeasureSpace, Nonempty (MeasureAlgebraIso μ S.measure) :=
  ⟨cantorMeasureModel X μ, ⟨cantorMeasureAlgebraIso X μ⟩⟩

end ThesisCommon
