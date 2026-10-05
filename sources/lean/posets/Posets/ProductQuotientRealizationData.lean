import Posets.ProductQuotientFull
import Posets.ProductQuotientIncidence
import Posets.ProductQuotientZero
import Posets.ProductQuotientBlocks

/-! Checked component data for the global quotient-algebra construction. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open ThesisCommon TopologicalSpace
namespace Posets

variable (𝕜 : Type) [RCLike 𝕜]

def HasContractiveSplit (Y C : Type) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C] : Prop :=
  ∃ θ : BoundedHom 𝕜 (Y →L[𝕜] Y) C,
  ∃ ρ : BoundedHom 𝕜 C (Y →L[𝕜] Y),
    StrongSplit 𝕜 Y C θ ρ ∧ Isometry ρ ∧ ‖θ.toContinuousLinearMap‖ ≤ 1

def quotientLeafFamily {P J : Type} (r : J → Option P) (𝒜 : P → Set (Set ℕ)) :
    J → Set (Set ℕ) := fun j => (r j).elim ∅ 𝒜

/-- Each field is witnessed below from an admissibility clause. `none` records
the empty-family c₀ padding used for zero factors. Nonempty coordinates make the
final countable sum uniform even when every target factor is zero. -/
structure ProductQuotientComponent (C : Type) [NormedRing C] [NormedAlgebra 𝕜 C] where
  Points : Type
  pointOrder : PartialOrder Points
  pointCountable : Countable Points
  Coordinates : Type
  coordinateCountable : Countable Coordinates
  coordinateNonempty : Nonempty Coordinates
  origin : Coordinates → Option Points
  realizes : letI := pointOrder
    ∀ 𝒜 : BoundedExtension Points → Set (Set ℕ),
      (∀ p, IsAlmostDisjoint (𝒜 p)) →
      ∀ ι : ∀ s t, Space 𝕜 (𝒜 s) →L[𝕜] Space 𝕜 (𝒜 t),
        FewOperators 𝕜 (fun p => Space 𝕜 (𝒜 p)) ι →
        HasContractiveSplit 𝕜
          (DependentCZeroSum 𝕜 (fun j => Space 𝕜
            (quotientLeafFamily origin (fun p => 𝒜 (middle p)) j))) C

attribute [instance] ProductQuotientComponent.pointOrder
  ProductQuotientComponent.pointCountable ProductQuotientComponent.coordinateCountable
  ProductQuotientComponent.coordinateNonempty

variable {𝕜} {C : Type} [NormedRing C] [NormedAlgebra 𝕜 C]

def finiteFullQuotientComponent (n : ℕ)
    (hc : RepresentedBy 𝕜 C (Fin (n + 1) → 𝕜) Set.univ) : ProductQuotientComponent 𝕜 C where
  Points := Fin 1
  pointOrder := inferInstance
  pointCountable := inferInstance
  Coordinates := Fin (n + 1)
  coordinateCountable := inferInstance
  coordinateNonempty := inferInstance
  origin := fun _ => some 0
  realizes := by
    intro 𝒜 _ ι h
    exact exists_productRepresentedFinite_strongSplit (h.1 (middle 0))
      (fewOperators_component_hasFewOperators h (middle 0)) hc

def infiniteFullQuotientComponent
    (hc : RepresentedBy 𝕜 C (cZero 𝕜) Set.univ) : ProductQuotientComponent 𝕜 C where
  Points := Fin 1
  pointOrder := inferInstance
  pointCountable := inferInstance
  Coordinates := ℕ
  coordinateCountable := inferInstance
  coordinateNonempty := inferInstance
  origin := fun _ => some 0
  realizes := by
    intro 𝒜 _ ι h
    exact exists_productRepresentedCZero_strongSplit (D := ℕ) (h.1 (middle 0))
      (fewOperators_component_hasFewOperators h (middle 0)) hc

def finiteIncidenceQuotientComponent (P : Type) [Fintype P] [PartialOrder P] [Nonempty P]
    (hc : RepresentedBy 𝕜 C (P → 𝕜) (finiteIncidenceOperators 𝕜 P)) :
    ProductQuotientComponent 𝕜 C where
  Points := OrderDual P
  pointOrder := inferInstance
  pointCountable := inferInstance
  Coordinates := P
  coordinateCountable := inferInstance
  coordinateNonempty := inferInstance
  origin := some
  realizes := by
    intro 𝒜 _ ι h
    apply exists_productFiniteIncidenceSum_strongSplit
      (middleFewOperators h) (middleCommonSubspace h)
    exact hc

def countableIncidenceQuotientComponent (P : Type) [Countable P] [PartialOrder P] [Nonempty P]
    (hc : RepresentedBy 𝕜 C (CZeroOn 𝕜 P) (incidenceOperators 𝕜 P)) :
    ProductQuotientComponent 𝕜 C where
  Points := OrderDual P
  pointOrder := inferInstance
  pointCountable := inferInstanceAs (Countable P)
  Coordinates := P
  coordinateCountable := inferInstance
  coordinateNonempty := inferInstance
  origin := some
  realizes := by
    intro 𝒜 _ ι h
    letI : Countable (OrderDual P) := inferInstanceAs (Countable P)
    apply exists_productCountableIncidence_strongSplit h
    exact hc

end Posets
