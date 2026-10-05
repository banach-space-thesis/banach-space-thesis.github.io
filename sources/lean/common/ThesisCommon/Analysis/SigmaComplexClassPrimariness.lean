import ThesisCommon.Analysis.SigmaComplexLatticeStructure

/-! Complex Banach spaces and primariness of their isomorphism classes. -/
universe u
namespace ThesisCommon

structure ComplexBanachSpace where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℂ Carrier]
  [completeSpace : CompleteSpace Carrier]

attribute [instance] ComplexBanachSpace.normedAddCommGroup ComplexBanachSpace.normedSpace
  ComplexBanachSpace.completeSpace
instance : CoeSort ComplexBanachSpace (Type u) := ⟨ComplexBanachSpace.Carrier⟩

def IsomorphicToComplexCK (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∃ K : Compactum.{u}, Nonempty (E ≃L[ℂ] C(K, ℂ))

def IsComplexPrimaryClass (P : ComplexBanachSpace.{u} → Prop) : Prop :=
  ∀ X Y Z : ComplexBanachSpace.{u}, P X → Nonempty (X ≃L[ℂ] (Y × Z)) → P Y ∨ P Z

end ThesisCommon
