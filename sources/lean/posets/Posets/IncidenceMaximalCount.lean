import Posets.IncidenceMaximalClosed

noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace Posets

variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P]
  [LocallyFiniteOrder P] [Fintype P]

/-- The genuine maximal closed ideals of the finite incidence operator algebra
are indexed by the elements of the poset. The empty poset is allowed. -/
def finiteIncidenceMaximalClosedIdealEquiv :
    ThesisCommon.MaximalClosedIdeals 𝕜
      (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) ≃ P := by
  let e₁ : ThesisCommon.MaximalClosedIdeals 𝕜
      (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) ≃
      {I : ThesisCommon.ClosedIdeal 𝕜 (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) //
        ThesisCommon.IsMaximalClosedIdeal 𝕜 I.val} :=
    (Equiv.subtypeSubtypeEquivSubtype (fun h => h.1)).symm
  let e₂ : {I : ThesisCommon.ClosedIdeal 𝕜
      (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P)) //
      ThesisCommon.IsMaximalClosedIdeal 𝕜 I.val} ≃ MaximalIntervalUpsets P :=
    (finiteIncidenceClosedIdealEquiv (𝕜 := 𝕜) (P := P)).subtypeEquiv
      finiteIncidenceClosedIdeal_maximal_iff
  exact e₁.trans (e₂.trans maximalIntervalUpsetsEquiv)

theorem finiteIncidenceMaximalClosedIdeal_card :
    Nat.card (ThesisCommon.MaximalClosedIdeals 𝕜
      (finiteIncidenceSubalgebra (𝕜 := 𝕜) (P := P))) = Fintype.card P := by
  rw [Nat.card_congr (finiteIncidenceMaximalClosedIdealEquiv (𝕜 := 𝕜) (P := P)),
    Nat.card_eq_fintype_card]

end Posets
