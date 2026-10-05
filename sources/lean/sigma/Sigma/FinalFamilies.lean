import Sigma.EnumeratedConstruction
import Sigma.IndexedAtoms

/-! Uniform names and atom equivalences for the two actual families constructed
by EnumeratedConstruction. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity

def EnumeratedConstruction.baseSets (D : EnumeratedConstruction) (side : Bool) (i : ConstructionIndex) : Set ℕ :=
  if side then (D.data i).choices.2.J₁ else (D.data i).choices.1.J₁

def EnumeratedConstruction.splitSets (D : EnumeratedConstruction) (side : Bool) (i : ConstructionIndex) : Set Point :=
  if side then (D.data i).choices.2.Z else (D.data i).choices.1.Z

def EnumeratedConstruction.family (D : EnumeratedConstruction) (side : Bool) : Set (Set Point) :=
  splitFamily (D.baseSets side) (D.splitSets side)

theorem EnumeratedConstruction.baseSets_infinite (D : EnumeratedConstruction) (side : Bool)
    (i : ConstructionIndex) : (D.baseSets side i).Infinite := by
  cases side
  · exact (D.data i).choices.1.infinite_J₂.mono (D.data i).choices.1.J₂_subset
  · exact (D.data i).choices.2.infinite_J₂.mono (D.data i).choices.2.J₂_subset

theorem EnumeratedConstruction.baseSets_subset (D : EnumeratedConstruction) (side : Bool)
    (i : ConstructionIndex) : D.baseSets side i ⊆ D.stock i := by
  cases side
  · exact (D.data i).choices.1.J₁_subset.trans (D.data i).choices.1.J₀_subset
  · exact (D.data i).choices.2.J₁_subset.trans (D.data i).choices.2.J₀_subset

theorem EnumeratedConstruction.baseSets_pairwise (D : EnumeratedConstruction) (side : Bool) :
    Pairwise (fun i j => (D.baseSets side i ∩ D.baseSets side j).Finite) :=
  fun i j hij => (D.stock_pairwise hij).subset
    (Set.inter_subset_inter (D.baseSets_subset side i) (D.baseSets_subset side j))

theorem EnumeratedConstruction.splits (D : EnumeratedConstruction) (side : Bool) (i : ConstructionIndex) :
    Splits (D.baseSets side i) (D.splitSets side i) := by
  cases side
  · exact (D.data i).choices.1.splits
  · exact (D.data i).choices.2.splits

theorem EnumeratedConstruction.family_almostDisjoint (D : EnumeratedConstruction) (side : Bool) :
    AlmostDisjoint (D.family side) :=
  splitFamily_almostDisjoint _ _ (D.baseSets_infinite side) (D.splits side) (D.baseSets_pairwise side)

theorem EnumeratedConstruction.family_infinite (D : EnumeratedConstruction) (side : Bool) :
    (D.family side).Infinite := by
  cases side
  · exact D.family_properties.1.2
  · exact D.family_properties.2.2

def EnumeratedConstruction.familyEquiv (D : EnumeratedConstruction) (side : Bool) :
    (ConstructionIndex × Bool) ≃ D.family side :=
  splitFamilyEquiv _ _ (D.baseSets_infinite side) (D.splits side) (D.baseSets_pairwise side)

def EnumeratedConstruction.infinityUltrafilter (D : EnumeratedConstruction) : Ultrafilter Point :=
  reservedInfinityUltrafilter D.reserve D.complement_infinite

theorem EnumeratedConstruction.infinityUltrafilter_free (D : EnumeratedConstruction) :
    (D.infinityUltrafilter : Filter Point) ≤ Filter.cofinite :=
  reservedInfinityUltrafilter_free _ _

theorem EnumeratedConstruction.infinityUltrafilter_avoids (D : EnumeratedConstruction) (side : Bool) :
    ∀ A ∈ D.family side, A ∉ D.infinityUltrafilter := by
  cases side
  · exact reservedInfinityUltrafilter_avoids_family _ _ (fun i => (D.data i).choices.1)
      D.reserve D.complement_infinite D.stock_inside
  · exact reservedInfinityUltrafilter_avoids_family _ _ (fun i => (D.data i).choices.2)
      D.reserve D.complement_infinite D.stock_inside

end SigmaNonprimarity
