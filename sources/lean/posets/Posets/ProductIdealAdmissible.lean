import Posets.ProductIdealRepresentation
import Posets.ProductIdealInfiniteIncidence

/-! The possible finite ideal-count profiles of the paper's admissible
factor algebras. Infinite incidence factors are excluded by their distinct
diagonal evaluation kernels. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open Set ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem idealCount_of_unique (P : Type) [PartialOrder P] [Fintype P]
    [Subsingleton P] [Nonempty P] : idealCount P = 2 := by
  let Q := {st : P × P // st.1 ≤ st.2}
  let e : IntervalUpsets P ≃ Set Q :=
    { toFun := Subtype.val
      invFun := fun W => ⟨W, fun i hi j _ _ => Subsingleton.elim i j ▸ hi⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let p : P := Classical.arbitrary P
  letI : Nonempty Q := ⟨⟨(p, p), le_rfl⟩⟩
  letI : Unique Q := { default := ⟨(p, p), le_rfl⟩, uniq := fun _ => Subsingleton.elim _ _ }
  rw [idealCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_set,
    Fintype.card_unique]
  norm_num

theorem closedIdeal_card_of_subsingleton {C : Type*}
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C] [Subsingleton C] :
    Nat.card (ClosedIdeal 𝕜 C) = 1 := by
  letI : Subsingleton (ClosedIdeal 𝕜 C) := ⟨fun I J => by
    apply Subtype.ext
    ext c
    constructor
    · intro _
      simpa only [Subsingleton.elim c 0] using J.property.2.1
    · intro _
      simpa only [Subsingleton.elim c 0] using I.property.2.1⟩
  letI : Nonempty (ClosedIdeal 𝕜 C) := ⟨⊤⟩
  exact Nat.card_unique

theorem maximalClosedIdeal_card_of_subsingleton {C : Type*}
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C] [Subsingleton C] :
    Nat.card (MaximalClosedIdeals 𝕜 C) = 0 := by
  letI : IsEmpty (MaximalClosedIdeals 𝕜 C) :=
    ⟨fun I => no_maximalClosedIdeal_of_subsingleton 𝕜 I.val I.property⟩
  simp

theorem representedBy_subsingleton_space {C E : Type}
    [NormedRing C] [NormedAlgebra 𝕜 C]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E]
    {S : Set (E →L[𝕜] E)} (h : RepresentedBy 𝕜 C E S) : Subsingleton C := by
  obtain ⟨f, hf, _⟩ := h
  exact ⟨fun a b => hf.injective (Subsingleton.elim _ _)⟩

/-- Every admissible factor with finitely many closed ideals is zero, a
three-ideal scalar c₀ operator factor, or has the ideal-count profile of a
nonempty finite incidence poset. Full matrix factors use a singleton poset. -/
theorem admissible_finite_closedIdeal_count_profile {C : Type}
    [NormedRing C] [NormedAlgebra 𝕜 C] [Finite (ClosedIdeal 𝕜 C)]
    (hC : AdmissibleAlgebra 𝕜 C) :
    Subsingleton C ∨
      (Nat.card (ClosedIdeal 𝕜 C) = 3 ∧ Nat.card (MaximalClosedIdeals 𝕜 C) = 1) ∨
      ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (_ : Nonempty P),
        Nat.card (ClosedIdeal 𝕜 C) = idealCount P ∧
          Nat.card (MaximalClosedIdeals 𝕜 C) = Fintype.card P := by
  rcases hC with hz | hmatrix | hfinite | hcountable | hcZero
  · exact Or.inl hz
  · obtain ⟨n, h⟩ := hmatrix
    obtain ⟨hi, hm⟩ := representedBy_fullFinite_ideal_counts h
    right; right
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · simpa only [idealCount_of_unique] using hi
    · simpa using hm
  · obtain ⟨P, hP, hPo, h⟩ := hfinite
    letI := hP
    letI := hPo
    rcases isEmpty_or_nonempty P with hempty | hnonempty
    · letI := hempty
      exact Or.inl (representedBy_subsingleton_space h)
    · letI := hnonempty
      letI : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder
      exact Or.inr (Or.inr ⟨P, hP, hPo, hnonempty, representedBy_finiteIncidence_ideal_counts h⟩)
  · obtain ⟨P, hP, hPo, h⟩ := hcountable
    letI := hP
    letI := hPo
    letI : Finite P := finite_poset_of_represented_incidence_finite_ideals h
    letI : Fintype P := Fintype.ofFinite P
    rcases isEmpty_or_nonempty P with hempty | hnonempty
    · letI := hempty
      letI : Subsingleton (CZeroOn 𝕜 P) := ⟨fun f g => by
        ext q
        exact isEmptyElim q.val⟩
      exact Or.inl (representedBy_subsingleton_space h)
    · letI := hnonempty
      letI : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder
      exact Or.inr (Or.inr ⟨P, inferInstance, hPo, hnonempty,
        representedBy_finiteIncidence_ideal_counts (representedBy_finiteIncidence_of_cZero h)⟩)
  · exact Or.inr (Or.inl (representedBy_fullCZero_ideal_counts hcZero))

end Posets
