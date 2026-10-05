import Posets.IncidenceIdealClassification

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Posets
variable {P : Type} [PartialOrder P]

def diagonalInterval (p : P) : PosetInterval P := ⟨(p, p), le_rfl⟩

/-- Maximality among proper upward-closed families of intervals. -/
def IsMaximalIntervalUpset (W : IntervalUpsets P) : Prop :=
  W.val ≠ Set.univ ∧ ∀ V : IntervalUpsets P, W.val ⊆ V.val → V = W ∨ V.val = Set.univ

def MaximalIntervalUpsets (P : Type) [PartialOrder P] :=
  {W : IntervalUpsets P // IsMaximalIntervalUpset W}

/-- Removing one diagonal leaves an upset: a diagonal contains no smaller interval. -/
def intervalsExceptDiagonal (p : P) : IntervalUpsets P :=
  ⟨{i | i ≠ diagonalInterval p}, by
    intro i hi j hs ht hj
    subst j
    apply hi
    apply Subtype.ext
    exact Prod.ext (le_antisymm (i.property.trans ht) hs)
      (le_antisymm ht (hs.trans i.property))⟩

@[simp] theorem mem_intervalsExceptDiagonal (p : P) (i : PosetInterval P) :
    i ∈ (intervalsExceptDiagonal p).val ↔ i ≠ diagonalInterval p := Iff.rfl

theorem intervalsExceptDiagonal_ne_univ (p : P) :
    (intervalsExceptDiagonal p).val ≠ Set.univ := by
  intro h
  have hm : diagonalInterval p ∈ (intervalsExceptDiagonal p).val := by rw [h]; trivial
  exact hm rfl

theorem intervalsExceptDiagonal_maximal (p : P) :
    IsMaximalIntervalUpset (intervalsExceptDiagonal p) := by
  refine ⟨intervalsExceptDiagonal_ne_univ p, ?_⟩
  intro V hV
  by_cases hd : diagonalInterval p ∈ V.val
  · right
    apply Set.eq_univ_of_forall
    intro i
    by_cases hi : i = diagonalInterval p
    · simpa only [hi] using hd
    · exact hV hi
  · left
    apply Subtype.ext
    apply Set.Subset.antisymm
    · intro i hi
      exact fun he => hd (he ▸ hi)
    · exact hV

theorem intervalsExceptDiagonal_injective : Function.Injective (intervalsExceptDiagonal (P := P)) := by
  intro p q h
  have hd : diagonalInterval p = diagonalInterval q := by
    by_contra hn
    have hm : diagonalInterval p ∈ (intervalsExceptDiagonal q).val := hn
    rw [← h] at hm
    exact hm rfl
  exact congrArg (fun i : PosetInterval P => i.val.1) hd

theorem maximalIntervalUpset_eq_exceptDiagonal (W : IntervalUpsets P)
    (hW : IsMaximalIntervalUpset W) : ∃ p, W = intervalsExceptDiagonal p := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ W.val := by
    by_contra hn
    exact hW.1 (Set.eq_univ_of_forall (by simpa using hn))
  have hd : diagonalInterval i.val.1 ∉ W.val := by
    intro h
    exact hi (W.property _ h i le_rfl i.property)
  have hsub : W.val ⊆ (intervalsExceptDiagonal i.val.1).val := by
    intro j hj he
    exact hd (he ▸ hj)
  rcases hW.2 _ hsub with heq | hbad
  · exact ⟨i.val.1, heq.symm⟩
  · exact False.elim (intervalsExceptDiagonal_ne_univ _ hbad)

/-- The maximal proper interval upsets are indexed exactly by the poset elements. -/
def maximalIntervalUpsetsEquiv : MaximalIntervalUpsets P ≃ P :=
  (Equiv.ofBijective
    (fun p : P => (⟨intervalsExceptDiagonal p, intervalsExceptDiagonal_maximal p⟩ :
      MaximalIntervalUpsets P))
    ⟨fun _ _ h => intervalsExceptDiagonal_injective (congrArg Subtype.val h), by
      intro W
      obtain ⟨p, hp⟩ := maximalIntervalUpset_eq_exceptDiagonal W.val W.property
      exact ⟨p, Subtype.ext hp.symm⟩⟩).symm

end Posets
