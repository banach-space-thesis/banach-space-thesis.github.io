import Posets.ProductIdealMaximal
import Posets.IncidenceMaximalCount

/-! The product and maximal-ideal counts for genuine finite incidence
operator algebras. These are the finite-poset factors in Proposition 8.4. -/

noncomputable section
namespace Posets
open ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] (P : ι → Type)
  [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)] [∀ i, LocallyFiniteOrder (P i)]

def finiteIncidenceProductClosedIdealEquiv :
    ClosedIdeal 𝕜 (∀ i, finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i)) ≃
      ∀ i, IntervalUpsets (P i) :=
  (productClosedIdealOrderIso (𝕜 := 𝕜)
    (fun i => finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i))).toEquiv.trans
    (Equiv.piCongrRight (fun i => finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P i)))

theorem finiteIncidenceProductClosedIdeal_card :
    Nat.card (ClosedIdeal 𝕜 (∀ i, finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i))) =
      ∏ i, idealCount (P i) := by
  rw [Nat.card_congr (finiteIncidenceProductClosedIdealEquiv (𝕜 := 𝕜) P), Nat.card_pi]
  rfl

def finiteIncidenceProductMaximalClosedIdealEquiv :
    MaximalClosedIdeals 𝕜 (∀ i, finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i)) ≃
      Σ i, P i :=
  (productMaximalClosedIdealEquiv (𝕜 := 𝕜)
    (fun i => finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i))).trans
    (Equiv.sigmaCongrRight (fun i => finiteIncidenceMaximalClosedIdealEquiv (𝕜 := 𝕜) (P := P i)))

theorem finiteIncidenceProductMaximalClosedIdeal_card :
    Nat.card (MaximalClosedIdeals 𝕜
      (∀ i, finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i))) =
      ∑ i, Fintype.card (P i) := by
  rw [Nat.card_congr (finiteIncidenceProductMaximalClosedIdealEquiv (𝕜 := 𝕜) P), Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card]

end Posets
