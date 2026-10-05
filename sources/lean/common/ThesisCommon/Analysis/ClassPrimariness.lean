import ThesisCommon.Analysis.BanachLattice

/-! Primariness of an isomorphism class of Banach spaces (as distinct from a primary space). -/
universe u
namespace ThesisCommon

/-- Whenever a member of the class splits into two Banach spaces, at least one
summand belongs to the class. Membership predicates should be isomorphism invariant. -/
def IsPrimaryClass (P : RealBanachSpace.{u} → Prop) : Prop :=
  ∀ X Y Z : RealBanachSpace.{u}, P X → Nonempty (X ≃L[ℝ] (Y × Z)) → P Y ∨ P Z

end ThesisCommon
