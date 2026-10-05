import PosetsCommon.Algebra
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Order.Atoms
import Mathlib.SetTheory.Cardinal.Finite

/-! Closed ideals in a finite product are exactly products of closed ideals.
Coordinate central idempotents recover each summand of an ideal element. -/

noncomputable section
open Set ThesisCommon
namespace Posets

variable {𝕜 : Type*} [RCLike 𝕜]

section General
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]

instance closedIdealOrderTop : OrderTop (ClosedIdeal 𝕜 A) where
  top := ⟨Set.univ, isClosed_univ, Set.mem_univ _,
    fun _ _ _ _ => Set.mem_univ _, fun _ _ _ => Set.mem_univ _,
    fun _ _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩⟩
  le_top _ := Set.subset_univ _

@[simp] theorem closedIdeal_top_val : (⊤ : ClosedIdeal 𝕜 A).val = Set.univ := rfl

def closedIdealSubmodule (I : ClosedIdeal 𝕜 A) : Submodule 𝕜 A where
  carrier := I.val
  zero_mem' := I.property.2.1
  add_mem' ha hb := I.property.2.2.1 _ ha _ hb
  smul_mem' c _ ha := I.property.2.2.2.1 c _ ha

theorem closedIdeal_maximal_iff_isCoatom (I : ClosedIdeal 𝕜 A) :
    IsMaximalClosedIdeal 𝕜 I.val ↔ IsCoatom I := by
  rw [isCoatom_iff_ge_of_le]
  constructor
  · intro hI
    refine ⟨fun h => hI.2.1 (congrArg Subtype.val h), ?_⟩
    intro J hJ hIJ
    rcases hI.2.2 J.val J.property hIJ with heq | htop
    · exact le_of_eq (Subtype.ext heq)
    · exact (hJ (Subtype.ext htop)).elim
  · rintro ⟨hproper, hmax⟩
    refine ⟨I.property, fun h => hproper (Subtype.ext h), ?_⟩
    intro J hJ hIJ
    by_cases htop : J = Set.univ
    · exact Or.inr htop
    · left
      exact Set.Subset.antisymm (hmax ⟨J, hJ⟩ (fun h => htop (congrArg Subtype.val h)) hIJ) hIJ

end General

section Product
variable {ι : Type*} [Fintype ι] (A : ι → Type*)
  [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra 𝕜 (A i)]

/-- Pull back a closed ideal along the coordinate inclusion. -/
def coordinateClosedIdeal (I : ClosedIdeal 𝕜 (∀ i, A i)) (i : ι) : ClosedIdeal 𝕜 (A i) := by
  classical
  refine ⟨Pi.single i ⁻¹' I.val, I.property.1.preimage (continuous_single i), ?_, ?_, ?_, ?_⟩
  · change Pi.single i 0 ∈ I.val
    simpa using I.property.2.1
  · intro a ha b hb
    change Pi.single i (a + b) ∈ I.val
    rw [Pi.single_add]
    exact I.property.2.2.1 _ ha _ hb
  · intro c a ha
    change Pi.single i (c • a) ∈ I.val
    rw [Pi.single_smul]
    exact I.property.2.2.2.1 c _ ha
  · intro a b hb
    change Pi.single i (a * b) ∈ I.val ∧ Pi.single i (b * a) ∈ I.val
    rw [Pi.single_mul, Pi.single_mul]
    exact I.property.2.2.2.2 (Pi.single i a) (Pi.single i b) hb

/-- The product of closed coordinate ideals, with the finite-product norm. -/
def productClosedIdeal (J : ∀ i, ClosedIdeal 𝕜 (A i)) : ClosedIdeal 𝕜 (∀ i, A i) := by
  refine ⟨{f | ∀ i, f i ∈ (J i).val}, ?_, ?_, ?_, ?_, ?_⟩
  · have he : {f : ∀ i, A i | ∀ i, f i ∈ (J i).val} =
        ⋂ i, (fun f : ∀ j, A j => f i) ⁻¹' (J i).val := by ext f; simp
    rw [he]
    exact isClosed_iInter (fun i => (J i).property.1.preimage (continuous_apply i))
  · exact fun i => (J i).property.2.1
  · exact fun a ha b hb i => (J i).property.2.2.1 _ (ha i) _ (hb i)
  · exact fun c a ha i => (J i).property.2.2.2.1 c _ (ha i)
  · intro a b hb
    exact ⟨fun i => ((J i).property.2.2.2.2 (a i) (b i) (hb i)).1,
      fun i => ((J i).property.2.2.2.2 (a i) (b i) (hb i)).2⟩

theorem single_coordinate_mem_closedIdeal (I : ClosedIdeal 𝕜 (∀ i, A i))
    {f : ∀ i, A i} (hf : f ∈ I.val) (i : ι) : f i ∈ (coordinateClosedIdeal A I i).val := by
  classical
  change Pi.single i (f i) ∈ I.val
  have he : Pi.single i (f i) = Pi.single i (1 : A i) * f := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  rw [he]
  exact (I.property.2.2.2.2 (Pi.single i (1 : A i)) f hf).1

theorem product_coordinateClosedIdeal (I : ClosedIdeal 𝕜 (∀ i, A i)) :
    productClosedIdeal A (coordinateClosedIdeal A I) = I := by
  classical
  apply Subtype.ext
  apply Set.Subset.antisymm
  · intro f hf
    have hsum : (∑ i, Pi.single i (f i)) ∈ (closedIdealSubmodule I) := by
      apply Submodule.sum_mem
      intro i _
      exact hf i
    rw [Finset.univ_sum_single] at hsum
    exact hsum
  · intro f hf i
    exact single_coordinate_mem_closedIdeal A I hf i

theorem coordinate_productClosedIdeal (J : ∀ i, ClosedIdeal 𝕜 (A i)) :
    coordinateClosedIdeal A (productClosedIdeal A J) = J := by
  classical
  funext i
  apply Subtype.ext
  ext a
  change (∀ j, Pi.single i a j ∈ (J j).val) ↔ a ∈ (J i).val
  constructor
  · intro h
    simpa using h i
  · intro ha j
    by_cases h : j = i
    · subst j; simpa using ha
    · simpa [Pi.single_eq_of_ne h] using (J j).property.2.1

/-- The full order classification of genuine closed two-sided ideals in a
finite product of unital normed algebras. Completeness is not required. -/
def productClosedIdealOrderIso :
    ClosedIdeal 𝕜 (∀ i, A i) ≃o (∀ i, ClosedIdeal 𝕜 (A i)) where
  toFun := coordinateClosedIdeal A
  invFun := productClosedIdeal A
  left_inv := product_coordinateClosedIdeal A
  right_inv := coordinate_productClosedIdeal A
  map_rel_iff' := by
    intro I J
    constructor
    · intro h f hf
      have hm : f ∈ (productClosedIdeal A (coordinateClosedIdeal A J)).val :=
        fun i => h i (single_coordinate_mem_closedIdeal A I hf i)
      simpa only [product_coordinateClosedIdeal] using hm
    · intro h i a ha
      exact h ha

theorem productClosedIdeal_card :
    Nat.card (ClosedIdeal 𝕜 (∀ i, A i)) = ∏ i, Nat.card (ClosedIdeal 𝕜 (A i)) := by
  rw [Nat.card_congr (productClosedIdealOrderIso (𝕜 := 𝕜) A).toEquiv, Nat.card_pi]

end Product
end Posets
