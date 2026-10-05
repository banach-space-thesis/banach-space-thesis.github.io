import Posets.PaperChainCatalanSplit
import Posets.PaperChainCatalanUpsets
import Posets.PaperChainCatalanTransport
import Posets.IncidenceIdealClosed
import Mathlib.Data.Finset.Sort

set_option synthInstance.maxHeartbeats 200000

/-! The Section 8 chain example: a d-point chain has Catalan(d+1)
interval upsets, hence that many closed ideals in its incidence algebra.
The count follows from the boundary-map bijection and the least-fixed-point
Catalan decomposition, rather than from a numerical identification. -/
noncomputable section
namespace Posets

theorem paper_chain_fin_idealCount (d : ℕ) : idealCount (Fin d) = catalan (d + 1) := by
  rw [idealCount, Nat.card_congr (paperChainUpsetsCatalanEquiv d), Nat.card_eq_fintype_card]
  exact paperCatalanMap_card (d + 1)

theorem paper_linearOrder_idealCount (P : Type*) [LinearOrder P] [Fintype P] :
    idealCount P = catalan (Fintype.card P + 1) := by
  rw [← idealCount_orderIso (Fintype.orderIsoFinOfCardEq P rfl)]
  exact paper_chain_fin_idealCount _

/-- Literal chain form: the given partial order is total. -/
theorem paper_chain_idealCount (P : Type*) [PartialOrder P] [Fintype P]
    (hchain : ∀ a b : P, a ≤ b ∨ b ≤ a) :
    idealCount P = catalan (Fintype.card P + 1) := by
  classical
  letI : LinearOrder P := { ‹PartialOrder P› with le_total := hchain, toDecidableLE := inferInstance }
  exact paper_linearOrder_idealCount P

theorem paper_chain_incidence_closedIdeal_card (𝕜 P : Type) [RCLike 𝕜]
    [LinearOrder P] [LocallyFiniteOrder P] [Fintype P] :
    Nat.card (ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P))) =
      catalan (Fintype.card P + 1) := by
  rw [finiteIncidenceClosedIdeal_card, paper_linearOrder_idealCount]

theorem paper_chain_first_values :
    idealCount (Fin 1) = 2 ∧ idealCount (Fin 2) = 5 ∧ idealCount (Fin 3) = 14 ∧
      idealCount (Fin 4) = 42 ∧ idealCount (Fin 5) = 132 := by
  norm_num [paper_chain_fin_idealCount, catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

end Posets
