import Sigma.FlipJL
import Sigma.CoefficientEnumeration
import ThesisCommon.Analysis.LpOperators

/-! A representative from every two-point orbit, and the single infinity
atom belonging to the symmetric coordinate of a crossed summand. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon

abbrev ReducedAtom := (Bool × (ℕ ⊕ ConstructionIndex)) ⊕ Unit

def pairedAtom (q : ℕ ⊕ ConstructionIndex) (bit : Bool) : IndexedAtom (ConstructionIndex × Bool) :=
  match q with
  | .inl n => .inl (n,bit)
  | .inr i => .inr (.inl (i,bit))

@[simp] theorem pairedAtom_flip (q : ℕ ⊕ ConstructionIndex) (bit : Bool) :
    indexedAtomFlip (pairedAtom q bit) = pairedAtom q (!bit) := by
  cases q <;> rfl

def reducedAtomMap (side : Bool) : ReducedAtom → FullAtom
  | .inl (copy,q) => (copy,pairedAtom q false)
  | .inr () => (!side,.inr (.inr ()))

def reducedAtomEmbedding (side : Bool) : ReducedAtom ↪ FullAtom where
  toFun := reducedAtomMap side
  inj' := by
    rintro (⟨s,n|i⟩ | ⟨⟩) (⟨t,m|j⟩ | ⟨⟩) <;> simp [reducedAtomMap,pairedAtom]

@[simp] theorem reducedAtomEmbedding_pair (side copy : Bool) (q : ℕ ⊕ ConstructionIndex) :
    reducedAtomEmbedding side (.inl (copy,q)) = (copy,pairedAtom q false) := rfl

@[simp] theorem reducedAtomEmbedding_infinity (side : Bool) :
    reducedAtomEmbedding side (.inr ()) = (!side,.inr (.inr ())) := rfl

theorem pairedAtom_true_not_representative (side copy : Bool) (q : ℕ ⊕ ConstructionIndex) :
    ¬ ∃ j, reducedAtomEmbedding side j = (copy,pairedAtom q true) := by
  rintro ⟨(⟨t,n|i⟩ | ⟨⟩),h⟩ <;> cases q <;>
    simp [reducedAtomEmbedding,reducedAtomMap,pairedAtom] at h

theorem extendReduced_pair_true (side copy : Bool) (q : ℕ ⊕ ConstructionIndex)
    (c : lp (fun _ : ReducedAtom => ℝ) 1) :
    lpExtend (𝕜 := ℝ) 1 (reducedAtomEmbedding side) c (copy,pairedAtom q true) = 0 := by
  change Function.extend (reducedAtomEmbedding side) c 0 (copy,pairedAtom q true) = 0
  exact Function.extend_apply' _ _ _ (pairedAtom_true_not_representative side copy q)

end SigmaNonprimarity
