import Posets.ProductIdealMatrix
import Posets.ProductIdealIncidence
import Posets.ProductIdealTransport
import Posets.ProductQuotientCoordinates
import Posets.FiniteIncidenceTransport

/-! Ideal counts depend on the represented operator algebra, with all
transport performed through genuine isometric multiplicative equivalences. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
open Set ThesisCommon
namespace Posets
variable {𝕜 C : Type} [RCLike 𝕜] [NormedRing C] [NormedAlgebra 𝕜 C]

theorem representedBy_fullFinite_ideal_counts {P : Type} [Fintype P] [Nonempty P]
    (h : RepresentedBy 𝕜 C (P → 𝕜) Set.univ) :
    Nat.card (ClosedIdeal 𝕜 C) = 2 ∧ Nat.card (MaximalClosedIdeals 𝕜 C) = 1 := by
  obtain ⟨e, he⟩ := representedBy_univ_coordinates h
  constructor
  · rw [Nat.card_congr (closedIdealLinearEquivOrderIso e.toContinuousLinearEquiv he).toEquiv]
    exact fullFiniteOperatorClosedIdeal_card
  · rw [Nat.card_congr (maximalClosedIdealLinearEquiv e.toContinuousLinearEquiv he)]
    exact fullFiniteOperatorMaximalClosedIdeal_card

theorem representedBy_fullCZero_ideal_counts
    (h : RepresentedBy 𝕜 C (cZero 𝕜) Set.univ) :
    Nat.card (ClosedIdeal 𝕜 C) = 3 ∧ Nat.card (MaximalClosedIdeals 𝕜 C) = 1 := by
  obtain ⟨e, he⟩ := representedBy_univ_coordinates h
  constructor
  · rw [Nat.card_congr (closedIdealLinearEquivOrderIso e.toContinuousLinearEquiv he).toEquiv]
    exact cZeroClosedIdeal_card
  · rw [Nat.card_congr (maximalClosedIdealLinearEquiv e.toContinuousLinearEquiv he)]
    exact cZeroMaximalClosedIdeal_card

theorem representedBy_finiteIncidence_ideal_counts {P : Type} [Fintype P]
    [PartialOrder P] [LocallyFiniteOrder P]
    (h : RepresentedBy 𝕜 C (P → 𝕜) (finiteIncidenceOperators 𝕜 P)) :
    Nat.card (ClosedIdeal 𝕜 C) = idealCount P ∧
      Nat.card (MaximalClosedIdeals 𝕜 C) = Fintype.card P := by
  obtain ⟨e, he⟩ := representedBy_subalgebra_coordinates
    (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) (by rwa [finiteIncidenceSubalgebra_carrier])
  constructor
  · rw [Nat.card_congr (closedIdealLinearEquivOrderIso e.toContinuousLinearEquiv he).toEquiv]
    exact finiteIncidenceClosedIdeal_card
  · rw [Nat.card_congr (maximalClosedIdealLinearEquiv e.toContinuousLinearEquiv he)]
    exact finiteIncidenceMaximalClosedIdeal_card

theorem representedBy_finiteIncidence_of_cZero {P : Type} [Fintype P] [PartialOrder P]
    (h : RepresentedBy 𝕜 C (CZeroOn 𝕜 P) (incidenceOperators 𝕜 P)) :
    RepresentedBy 𝕜 C (P → 𝕜) (finiteIncidenceOperators 𝕜 P) := by
  obtain ⟨f, hf, hr⟩ := h
  let e := finiteCZeroOperatorEquiv 𝕜 P
  let g : BoundedHom 𝕜 C ((P → 𝕜) →L[𝕜] (P → 𝕜)) :=
    { toContinuousLinearMap := e.toContinuousLinearEquiv.toContinuousLinearMap.comp f.toContinuousLinearMap
      map_mul' := by
        intro a b
        change e (f (a * b)) = e (f a) * e (f b)
        rw [f.map_mul', finiteCZeroOperatorEquiv_mul] }
  refine ⟨g, e.isometry.comp hf, ?_⟩
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    apply (finite_incidence_transport (f a)).mpr
    rw [← hr]
    exact ⟨a, rfl⟩
  · intro hT
    obtain ⟨U, rfl⟩ := e.surjective T
    have hU : U ∈ Set.range f := by
      rw [hr]
      exact (finite_incidence_transport U).mp hT
    obtain ⟨a, ha⟩ := hU
    exact ⟨a, congrArg e ha⟩

end Posets
