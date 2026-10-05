import Posets.ProductIdealIncidence
import Posets.ProductIdealCZero

/-! The finite-product numerical formulas used in Proposition 8.4.
These count ideals of the actual quotient-model algebras; realization as an
operator quotient and the converse remain separate assertions. -/

noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable (r : ℕ) {k : ℕ} (P : Fin k → Type)
  [∀ i, Fintype (P i)] [∀ i, PartialOrder (P i)] [∀ i, LocallyFiniteOrder (P i)]

def cZeroIncidenceFactor : Fin r ⊕ Fin k → Type
  | .inl _ => cZero 𝕜 →L[𝕜] cZero 𝕜
  | .inr i => finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P i)

instance cZeroIncidenceFactor_normedRing (i : Fin r ⊕ Fin k) :
    NormedRing (cZeroIncidenceFactor (𝕜 := 𝕜) r P i) := by
  cases i <;> dsimp [cZeroIncidenceFactor] <;> infer_instance

instance cZeroIncidenceFactor_normedAlgebra (i : Fin r ⊕ Fin k) :
    NormedAlgebra 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i) := by
  cases i <;> dsimp [cZeroIncidenceFactor] <;> infer_instance

theorem cZeroIncidenceFactor_closedIdeal_card (i : Fin r ⊕ Fin k) :
    Nat.card (ClosedIdeal 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) =
      Sum.elim (fun _ => 3) (fun j => idealCount (P j)) i := by
  cases i with
  | inl i => exact cZeroClosedIdeal_card
  | inr i => exact finiteIncidenceClosedIdeal_card

instance cZeroIncidenceFactor_finite_maximalClosedIdeals (i : Fin r ⊕ Fin k) :
    Finite (MaximalClosedIdeals 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) := by
  cases i with
  | inl i =>
      exact Finite.of_equiv (Fin 1) (cZeroMaximalClosedIdealEquivFinOne (𝕜 := 𝕜)).symm
  | inr i =>
      exact Finite.of_equiv (P i)
        (finiteIncidenceMaximalClosedIdealEquiv (𝕜 := 𝕜) (P := P i)).symm

theorem cZeroIncidenceFactor_maximalClosedIdeal_card (i : Fin r ⊕ Fin k) :
    Nat.card (MaximalClosedIdeals 𝕜 (cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) =
      Sum.elim (fun _ => 1) (fun j => Fintype.card (P j)) i := by
  cases i with
  | inl i => exact cZeroMaximalClosedIdeal_card
  | inr i => exact finiteIncidenceMaximalClosedIdeal_card

/-- The closed-ideal count is three per scalar c₀ operator factor, times the
interval-upset count of each finite incidence operator factor. -/
theorem cZeroIncidenceProduct_closedIdeal_card :
    Nat.card (ClosedIdeal 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) =
      3 ^ r * ∏ i, idealCount (P i) := by
  rw [productClosedIdeal_card]
  simp_rw [cZeroIncidenceFactor_closedIdeal_card]
  simp [Fintype.prod_sum_type]

/-- Maximal ideals are contributed once by each c₀ operator factor and once
by each element of each finite poset. The empty finite product is allowed. -/
theorem cZeroIncidenceProduct_maximalClosedIdeal_card :
    Nat.card (MaximalClosedIdeals 𝕜 (∀ i, cZeroIncidenceFactor (𝕜 := 𝕜) r P i)) =
      r + ∑ i, Fintype.card (P i) := by
  rw [productMaximalClosedIdeal_card]
  simp_rw [cZeroIncidenceFactor_maximalClosedIdeal_card]
  simp [Fintype.sum_sum_type]

end Posets
