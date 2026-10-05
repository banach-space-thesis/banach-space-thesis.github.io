import Sigma.ComplexIndexedAtoms
import Sigma.ComplexJLEvaluation
import Sigma.FamilyCoefficients

/-! Evaluation on a family generator is its atomic base mass plus its one
family coefficient. This explicitly accounts for every other family atom and
the infinity atom, whose evaluations on this generator vanish. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] complexJLGroup complexJLSpace complexJLDualGroup complexJLDualSpace

theorem complexIndexedJLDual_family {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : ComplexJL B →L[ℂ] ℂ) (i : Λ) :
    φ ⟨complexCharacteristic (e i).val,complexCharacteristic_mem_ComplexJL (e i).property⟩ =
      (∑' p : (e i).val, complexIndexedJLDualEquiv hB hInf e φ (.inl p.val)) +
        complexIndexedJLDualEquiv hB hInf e φ (.inr (.inl i)) := by
  classical
  let c := complexIndexedJLDualEquiv hB hInf e φ
  let L : Point → ℂ := (e i).val.indicator (fun p => c (.inl p))
  let R : Λ → ℂ := fun j => if j = i then c (.inr (.inl i)) else 0
  let Z : Unit → ℂ := fun _ => 0
  have hL : HasSum L (∑' p : (e i).val, c (.inl p.val)) := by
    rw [tsum_subtype (e i).val (fun p => c (.inl p))]
    exact (((complexLpOneHasSumNorm c).summable.of_norm.comp_injective Sum.inl_injective).indicator _).hasSum
  have hR : HasSum R (c (.inr (.inl i))) := hasSum_ite_eq i _
  have hZ : HasSum Z 0 := hasSum_zero
  have hs : HasSum (Sum.elim L (Sum.elim R Z))
      ((∑' p : (e i).val, c (.inl p.val)) + c (.inr (.inl i))) := by
    simpa only [add_zero] using hL.sum (f := Sum.elim L (Sum.elim R Z))
      (hR.sum (f := Sum.elim R Z) hZ)
  have heval := complexIndexedJLDual_apply_hasSum hB hInf e φ
    ⟨complexCharacteristic (e i).val,complexCharacteristic_mem_ComplexJL (e i).property⟩
  rw [complexJLContinuous_family] at heval
  have hfun : (fun p => c p * (tailFunction hB (e i) (compactumAtomEquiv e p) : ℂ)) =
      Sum.elim L (Sum.elim R Z) := by
    funext p
    rcases p with p | (j | u)
    · by_cases hp : p ∈ (e i).val <;>
        simp [L,compactumAtomEquiv_base,tailFunction_base,Set.indicator_apply,hp]
    · simp only [compactumAtomEquiv_family,tailFunction_inr,Equiv.apply_eq_iff_eq]
      by_cases h : j = i
      · subst j; simp [R]
      · simp [R,h]
    · cases u
      simp [Z]
  change HasSum (fun p => c p * (tailFunction hB (e i) (compactumAtomEquiv e p) : ℂ)) _ at heval
  rw [hfun] at heval
  exact heval.unique hs

end SigmaNonprimarity


