import Posets.IncidenceIdealClosed
import Posets.BipartiteCount

/-! Proposition 8.5's formula for the genuine closed ideals of the
finite bipartite incidence operator algebra. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option synthInstance.maxHeartbeats 200000
namespace Posets
variable (𝕜 : Type) [RCLike 𝕜] (L R : Type) [Fintype L] [Fintype R] (E : L → R → Prop)
theorem bipartiteIncidenceClosedIdeal_count :
    letI : PartialOrder (L ⊕ R) := bipartiteOrder E
    letI : LocallyFiniteOrder (L ⊕ R) := Fintype.toLocallyFiniteOrder
    Nat.card (ThesisCommon.ClosedIdeal 𝕜
      (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := L ⊕ R))) =
      ∑ I : Finset L, ∑ J : Finset R, 2 ^ ((I.product J).filter (fun e => E e.1 e.2)).card := by
  letI : PartialOrder (L ⊕ R) := bipartiteOrder E
  letI : LocallyFiniteOrder (L ⊕ R) := Fintype.toLocallyFiniteOrder
  rw [finiteIncidenceClosedIdeal_card]
  exact proposition_8_5_proof E

end Posets
