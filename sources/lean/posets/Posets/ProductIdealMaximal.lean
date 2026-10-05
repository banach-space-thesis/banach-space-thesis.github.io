import Posets.ProductIdealClosed

/-! A maximal ideal of a finite product has exactly one proper coordinate.
Consequently maximal closed ideals are indexed by a coordinate and a maximal
closed ideal of that factor. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon
namespace Posets

section Order
variable {ι : Type*} {β : ι → Type*} [∀ i, PartialOrder (β i)] [∀ i, OrderTop (β i)]

theorem pi_isCoatom_iff {f : ∀ i, β i} :
    IsCoatom f ↔ ∃ i, IsCoatom (f i) ∧ ∀ j, j ≠ i → f j = ⊤ :=
  Pi.isAtom_iff (π := fun i => (β i)ᵒᵈ)

theorem pi_isCoatom_iff_eq_update {f : ∀ i, β i} :
    IsCoatom f ↔ ∃ i a, IsCoatom a ∧ f = Function.update ⊤ i a :=
  Pi.isAtom_iff_eq_single (π := fun i => (β i)ᵒᵈ)

def coatomPiInsertion (x : Σ i, {a : β i // IsCoatom a}) :
    {f : ∀ i, β i // IsCoatom f} :=
  ⟨Function.update ⊤ x.1 x.2.val,
    pi_isCoatom_iff_eq_update.mpr ⟨x.1, x.2.val, x.2.property, rfl⟩⟩

theorem coatomPiInsertion_bijective :
    Function.Bijective (coatomPiInsertion (β := β)) := by
  constructor
  · rintro ⟨i, ⟨a, ha⟩⟩ ⟨j, ⟨b, hb⟩⟩ he
    have hf := congrArg Subtype.val he
    change Function.update (⊤ : ∀ i, β i) i a = Function.update ⊤ j b at hf
    have hij : i = j := by
      by_contra hne
      have hv := congrFun hf i
      simp only [Function.update_self, Function.update_of_ne hne] at hv
      exact ha.ne_top hv
    subst j
    have hab : a = b := by simpa using congrFun hf i
    subst b
    rfl
  · rintro ⟨f, hf⟩
    obtain ⟨i, a, ha, hfa⟩ := pi_isCoatom_iff_eq_update.mp hf
    exact ⟨⟨i, ⟨a, ha⟩⟩, Subtype.ext hfa.symm⟩

def piCoatomSigmaEquiv :
    {f : ∀ i, β i // IsCoatom f} ≃ Σ i, {a : β i // IsCoatom a} :=
  (Equiv.ofBijective coatomPiInsertion coatomPiInsertion_bijective).symm

end Order

variable {𝕜 : Type*} [RCLike 𝕜]

def maximalClosedIdealEquivCoatom {A : Type*}
    [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A] :
    MaximalClosedIdeals 𝕜 A ≃ {I : ClosedIdeal 𝕜 A // IsCoatom I} :=
  (Equiv.subtypeSubtypeEquivSubtype
    (fun (h : IsMaximalClosedIdeal 𝕜 _) => h.1)).symm.trans
    (Equiv.subtypeEquivRight closedIdeal_maximal_iff_isCoatom)

variable {ι : Type*} [Fintype ι] (A : ι → Type*)
  [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra 𝕜 (A i)]

/-- Maximality is exactly one maximal coordinate with all others unrestricted. -/
theorem productClosedIdeal_maximal_iff (I : ClosedIdeal 𝕜 (∀ i, A i)) :
    IsMaximalClosedIdeal 𝕜 I.val ↔
      ∃ i, IsMaximalClosedIdeal 𝕜 (coordinateClosedIdeal A I i).val ∧
        ∀ j, j ≠ i → (coordinateClosedIdeal A I j).val = Set.univ := by
  rw [closedIdeal_maximal_iff_isCoatom,
    ← (productClosedIdealOrderIso (𝕜 := 𝕜) A).isCoatom_iff, pi_isCoatom_iff]
  apply exists_congr
  intro i
  rw [closedIdeal_maximal_iff_isCoatom]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro _
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Genuine maximal closed ideals of a finite product correspond to the
disjoint union of the maximal closed ideal sets of its factors. -/
def productMaximalClosedIdealEquiv :
    MaximalClosedIdeals 𝕜 (∀ i, A i) ≃ Σ i, MaximalClosedIdeals 𝕜 (A i) :=
  maximalClosedIdealEquivCoatom.trans
    (((productClosedIdealOrderIso (𝕜 := 𝕜) A).toEquiv.subtypeEquiv
      (fun I => ((productClosedIdealOrderIso (𝕜 := 𝕜) A).isCoatom_iff I).symm)).trans
      (piCoatomSigmaEquiv.trans
        (Equiv.sigmaCongrRight (fun _ => maximalClosedIdealEquivCoatom.symm))))

theorem productMaximalClosedIdeal_card
    [∀ i, Finite (MaximalClosedIdeals 𝕜 (A i))] :
    Nat.card (MaximalClosedIdeals 𝕜 (∀ i, A i)) =
      ∑ i, Nat.card (MaximalClosedIdeals 𝕜 (A i)) := by
  rw [Nat.card_congr (productMaximalClosedIdealEquiv (𝕜 := 𝕜) A), Nat.card_sigma]

end Posets
