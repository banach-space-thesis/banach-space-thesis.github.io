import Sigma.ComplexEnumeratedConstruction
import Sigma.IndexedAtoms

/-! Uniform names and atom equivalences for the two actual families constructed
by ComplexEnumeratedConstruction. -/
noncomputable section
open Set Filter ThesisCommon
namespace SigmaNonprimarity

def ComplexEnumeratedConstruction.baseSets (D : ComplexEnumeratedConstruction) (side : Bool) (i : ConstructionIndex) : Set ℕ :=
  if side then (D.data i).choices.2.J₁ else (D.data i).choices.1.J₁

def ComplexEnumeratedConstruction.splitSets (D : ComplexEnumeratedConstruction) (side : Bool) (i : ConstructionIndex) : Set Point :=
  if side then (D.data i).choices.2.Z else (D.data i).choices.1.Z

def ComplexEnumeratedConstruction.family (D : ComplexEnumeratedConstruction) (side : Bool) : Set (Set Point) :=
  splitFamily (D.baseSets side) (D.splitSets side)

theorem ComplexEnumeratedConstruction.baseSets_infinite (D : ComplexEnumeratedConstruction) (side : Bool)
    (i : ConstructionIndex) : (D.baseSets side i).Infinite := by
  cases side
  · exact (D.data i).choices.1.infinite_J₂.mono (D.data i).choices.1.J₂_subset
  · exact (D.data i).choices.2.infinite_J₂.mono (D.data i).choices.2.J₂_subset

theorem ComplexEnumeratedConstruction.baseSets_subset (D : ComplexEnumeratedConstruction) (side : Bool)
    (i : ConstructionIndex) : D.baseSets side i ⊆ D.stock i := by
  cases side
  · exact (D.data i).choices.1.J₁_subset.trans (D.data i).choices.1.J₀_subset
  · exact (D.data i).choices.2.J₁_subset.trans (D.data i).choices.2.J₀_subset

theorem ComplexEnumeratedConstruction.baseSets_pairwise (D : ComplexEnumeratedConstruction) (side : Bool) :
    Pairwise (fun i j => (D.baseSets side i ∩ D.baseSets side j).Finite) :=
  fun i j hij => (D.stock_pairwise hij).subset
    (Set.inter_subset_inter (D.baseSets_subset side i) (D.baseSets_subset side j))

theorem ComplexEnumeratedConstruction.splits (D : ComplexEnumeratedConstruction) (side : Bool) (i : ConstructionIndex) :
    Splits (D.baseSets side i) (D.splitSets side i) := by
  cases side
  · exact (D.data i).choices.1.splits
  · exact (D.data i).choices.2.splits

theorem ComplexEnumeratedConstruction.family_almostDisjoint (D : ComplexEnumeratedConstruction) (side : Bool) :
    AlmostDisjoint (D.family side) :=
  splitFamily_almostDisjoint _ _ (D.baseSets_infinite side) (D.splits side) (D.baseSets_pairwise side)

theorem ComplexEnumeratedConstruction.family_infinite (D : ComplexEnumeratedConstruction) (side : Bool) :
    (D.family side).Infinite := by
  cases side
  · exact D.family_properties.1.2
  · exact D.family_properties.2.2

def ComplexEnumeratedConstruction.familyEquiv (D : ComplexEnumeratedConstruction) (side : Bool) :
    (ConstructionIndex × Bool) ≃ D.family side :=
  splitFamilyEquiv _ _ (D.baseSets_infinite side) (D.splits side) (D.baseSets_pairwise side)

def ComplexEnumeratedConstruction.infinityUltrafilter (D : ComplexEnumeratedConstruction) : Ultrafilter Point :=
  reservedInfinityUltrafilter D.reserve D.complement_infinite

theorem ComplexEnumeratedConstruction.infinityUltrafilter_free (D : ComplexEnumeratedConstruction) :
    (D.infinityUltrafilter : Filter Point) ≤ Filter.cofinite :=
  reservedInfinityUltrafilter_free _ _

theorem ComplexEnumeratedConstruction.infinityUltrafilter_avoids (D : ComplexEnumeratedConstruction) (side : Bool) :
    ∀ A ∈ D.family side, A ∉ D.infinityUltrafilter := by
  intro A hA
  apply reservedInfinityUltrafilter_avoids
  have hJ (i : ConstructionIndex) : D.baseSets side i ⊆ D.reserve :=
    (D.baseSets_subset side i).trans (D.stock_inside i)
  rcases hA with (⟨i,rfl⟩ | ⟨i,rfl⟩)
  · exact fun p hp => hJ i ((D.splits side i).1 hp)
  · exact fun p hp => hJ i hp.1

end SigmaNonprimarity


