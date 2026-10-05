import Posets.ProductIdealTransport
import Posets.ProductIdealActive
import Posets.SemisimpleQuotientTools

/-! A bounded product with only finitely many active coordinates is
isometrically its finite prefix. Its ideal counts therefore reduce to the
finite-product classifications. -/

noncomputable section
open ThesisCommon
open scoped ENNReal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
variable (C : ℕ → Type) [∀ m, NormedRing (C m)] [∀ m, NormedAlgebra 𝕜 (C m)]
variable (n : ℕ) (hz : ∀ m, n ≤ m → Subsingleton (C m))

theorem normedProductPrefixLinearEquiv_norm (x : NormedProduct C) :
    ‖normedProductPrefixLinearEquiv (𝕜 := 𝕜) C n hz x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i.val
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro m
    by_cases h : m < n
    · exact norm_le_pi_norm (normedProductPrefixLinearEquiv (𝕜 := 𝕜) C n hz x) ⟨m, h⟩
    · letI := hz m (Nat.le_of_not_gt h)
      rw [Subsingleton.elim (x m) 0, norm_zero]
      exact norm_nonneg _

def normedProductPrefixIsometryEquiv : NormedProduct C ≃ₗᵢ[𝕜] (Π i : Fin n, C i.val) :=
  { normedProductPrefixLinearEquiv (𝕜 := 𝕜) C n hz with
    norm_map' := normedProductPrefixLinearEquiv_norm C n hz }

def normedProductPrefixClosedIdealOrderIso :
    ClosedIdeal 𝕜 (NormedProduct C) ≃o (∀ i : Fin n, ClosedIdeal 𝕜 (C i.val)) :=
  (closedIdealLinearEquivOrderIso (normedProductPrefixIsometryEquiv (𝕜 := 𝕜) C n hz).toContinuousLinearEquiv
    (normedProductPrefixLinearEquiv_map_mul C n hz)).trans
      (productClosedIdealOrderIso (𝕜 := 𝕜) (fun i : Fin n => C i.val))

include hz in
theorem normedProductPrefix_closedIdeal_card :
    Nat.card (ClosedIdeal 𝕜 (NormedProduct C)) =
      ∏ i : Fin n, Nat.card (ClosedIdeal 𝕜 (C i.val)) := by
  rw [Nat.card_congr (normedProductPrefixClosedIdealOrderIso (𝕜 := 𝕜) C n hz).toEquiv,
    Nat.card_pi]

def normedProductPrefixMaximalClosedIdealEquiv :
    MaximalClosedIdeals 𝕜 (NormedProduct C) ≃ Σ i : Fin n, MaximalClosedIdeals 𝕜 (C i.val) :=
  (maximalClosedIdealLinearEquiv (normedProductPrefixIsometryEquiv (𝕜 := 𝕜) C n hz).toContinuousLinearEquiv
    (normedProductPrefixLinearEquiv_map_mul C n hz)).trans
      (productMaximalClosedIdealEquiv (𝕜 := 𝕜) (fun i : Fin n => C i.val))

include hz in
theorem normedProductPrefix_maximalClosedIdeal_card
    [∀ i : Fin n, Finite (MaximalClosedIdeals 𝕜 (C i.val))] :
    Nat.card (MaximalClosedIdeals 𝕜 (NormedProduct C)) =
      ∑ i : Fin n, Nat.card (MaximalClosedIdeals 𝕜 (C i.val)) := by
  rw [Nat.card_congr (normedProductPrefixMaximalClosedIdealEquiv (𝕜 := 𝕜) C n hz), Nat.card_sigma]

/-- The numerical reduction in the converse: a finite ideal set is the
product of the ideal sets of a sufficiently long finite prefix. -/
theorem normedProduct_finite_closedIdeal_card_reduction
    [Finite (ClosedIdeal 𝕜 (NormedProduct C))] :
    ∃ N : ℕ, (∀ m, N ≤ m → Subsingleton (C m)) ∧
      Nat.card (ClosedIdeal 𝕜 (NormedProduct C)) =
        ∏ i : Fin N, Nat.card (ClosedIdeal 𝕜 (C i.val)) := by
  obtain ⟨N, hN⟩ := normedProduct_eventually_subsingleton_of_finite_closedIdeals (𝕜 := 𝕜) C
  exact ⟨N, hN, normedProductPrefix_closedIdeal_card C N hN⟩

end Posets
