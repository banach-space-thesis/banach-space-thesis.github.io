import Sigma.IndexedAtoms
import Sigma.JLEvaluation

/-! Evaluation on a family generator is its atomic base mass plus its one
family coefficient. This explicitly accounts for every other family atom and
the infinity atom, whose evaluations on this generator vanish. -/
noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

theorem tailFunction_base {B : Set (Set Point)} (hB : AlmostDisjoint B) (b : B) (p : Point) :
    tailFunction hB b (↑(Sum.inl p : MrowkaBase B)) = characteristic b.val p :=
  congrArg (fun f : Ambient => f p) (restrict_tailFunction hB b)

theorem indexedJLDual_family {Λ : Type} {B : Set (Set Point)}
    (hB : AlmostDisjoint B) (hInf : B.Infinite) (e : Λ ≃ B) (φ : JL B →L[ℝ] ℝ) (i : Λ) :
    φ ⟨characteristic (e i).val,characteristic_mem_JL (e i).property⟩ =
      (∑' p : (e i).val, indexedJLDualEquiv hB hInf e φ (.inl p.val)) +
        indexedJLDualEquiv hB hInf e φ (.inr (.inl i)) := by
  classical
  let c := indexedJLDualEquiv hB hInf e φ
  let L : Point → ℝ := (e i).val.indicator (fun p => c (.inl p))
  let R : Λ → ℝ := fun j => if j = i then c (.inr (.inl i)) else 0
  let Z : Unit → ℝ := fun _ => 0
  have hL : HasSum L (∑' p : (e i).val, c (.inl p.val)) := by
    rw [tsum_subtype (e i).val (fun p => c (.inl p))]
    exact (((lp_one_hasSum_norm c).summable.of_norm.comp_injective Sum.inl_injective).indicator _).hasSum
  have hR : HasSum R (c (.inr (.inl i))) := hasSum_ite_eq i _
  have hZ : HasSum Z 0 := hasSum_zero
  have hs : HasSum (Sum.elim L (Sum.elim R Z))
      ((∑' p : (e i).val, c (.inl p.val)) + c (.inr (.inl i))) := by
    simpa only [add_zero] using hL.sum (f := Sum.elim L (Sum.elim R Z))
      (hR.sum (f := Sum.elim R Z) hZ)
  have heval := indexedJLDual_apply_hasSum hB hInf e φ
    ⟨characteristic (e i).val,characteristic_mem_JL (e i).property⟩
  rw [jlContinuous_family] at heval
  have hfun : (fun p => c p * tailFunction hB (e i) (compactumAtomEquiv e p)) =
      Sum.elim L (Sum.elim R Z) := by
    funext p
    rcases p with p | (j | u)
    · simp [L,compactumAtomEquiv_base,tailFunction_base,Set.indicator_apply]
    · simp only [compactumAtomEquiv_family,tailFunction_inr,Equiv.apply_eq_iff_eq]
      by_cases h : j = i
      · subst j; simp [R]
      · simp [R,h]
    · cases u
      simp [Z]
  change HasSum (fun p => c p * tailFunction hB (e i) (compactumAtomEquiv e p)) _ at heval
  rw [hfun] at heval
  exact heval.unique hs

end SigmaNonprimarity
