import Posets.IdealCounts
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Posets
variable {L R : Type} (E : L → R → Prop)

abbrev BipartiteUpsets := @IntervalUpsets (L ⊕ R) (bipartiteOrder E)

abbrev BipartiteInterval := {st : (L ⊕ R) × (L ⊕ R) // BipartiteLE E st.1 st.2}

def bipartiteLeftDiagonalInterval (l : L) : BipartiteInterval E := ⟨(.inl l, .inl l), rfl⟩
def bipartiteRightDiagonalInterval (r : R) : BipartiteInterval E := ⟨(.inr r, .inr r), rfl⟩
def bipartiteEdgeInterval (l : L) (r : R) (h : E l r) : BipartiteInterval E :=
  ⟨(.inl l, .inr r), h⟩

/-- The edges whose two diagonal intervals are missing. -/
def bipartiteFreeEdges (I : Finset L) (J : Finset R) : Finset (L × R) :=
  (I.product J).filter (fun e => E e.1 e.2)

@[simp] theorem mem_bipartiteFreeEdges (I : Finset L) (J : Finset R) (e : L × R) :
    e ∈ bipartiteFreeEdges E I J ↔ e.1 ∈ I ∧ e.2 ∈ J ∧ E e.1 e.2 := by
  simp [bipartiteFreeEdges, and_assoc]

/-- Missing diagonal intervals, followed by a freely chosen set of missing edges. -/
def BipartiteChoices := Σ I : Finset L, Σ J : Finset R, Set (bipartiteFreeEdges E I J)

def bipartiteChosenMembership (I : Finset L) (J : Finset R)
    (S : Set (bipartiteFreeEdges E I J)) : (L ⊕ R) → (L ⊕ R) → Prop
  | .inl l, .inl _ => l ∉ I
  | .inl l, .inr r => ¬ ∃ h : (l, r) ∈ bipartiteFreeEdges E I J, ⟨(l, r), h⟩ ∈ S
  | .inr _, .inl _ => False
  | .inr r, .inr _ => r ∉ J

theorem bipartiteChosenMembership_upward (I : Finset L) (J : Finset R)
    (S : Set (bipartiteFreeEdges E I J)) :
    ∀ i : BipartiteInterval E, bipartiteChosenMembership E I J S i.val.1 i.val.2 →
      ∀ j : BipartiteInterval E, BipartiteLE E j.val.1 i.val.1 → BipartiteLE E i.val.2 j.val.2 →
        bipartiteChosenMembership E I J S j.val.1 j.val.2 := by
  rintro ⟨⟨a, b⟩, hab⟩ hi ⟨⟨c, d⟩, hcd⟩ hca hbd
  change BipartiteLE E a b at hab
  change BipartiteLE E c d at hcd
  change BipartiteLE E c a at hca
  change BipartiteLE E b d at hbd
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [BipartiteLE, bipartiteChosenMembership]
  simp only [BipartiteLE] at hab
  simp_all

def bipartiteDecode (x : BipartiteChoices E) : BipartiteUpsets E :=
  ⟨{i | bipartiteChosenMembership E x.1 x.2.1 x.2.2 i.val.1 i.val.2},
    bipartiteChosenMembership_upward E x.1 x.2.1 x.2.2⟩

@[simp] theorem bipartiteDecode_left (I : Finset L) (J : Finset R)
    (S : Set (bipartiteFreeEdges E I J)) (l : L) :
    bipartiteLeftDiagonalInterval E l ∈ (bipartiteDecode E ⟨I, J, S⟩).val ↔ l ∉ I := Iff.rfl

@[simp] theorem bipartiteDecode_right (I : Finset L) (J : Finset R)
    (S : Set (bipartiteFreeEdges E I J)) (r : R) :
    bipartiteRightDiagonalInterval E r ∈ (bipartiteDecode E ⟨I, J, S⟩).val ↔ r ∉ J := Iff.rfl

@[simp] theorem bipartiteDecode_free_edge (I : Finset L) (J : Finset R)
    (S : Set (bipartiteFreeEdges E I J)) (e : bipartiteFreeEdges E I J) :
    bipartiteEdgeInterval E e.val.1 e.val.2
      ((mem_bipartiteFreeEdges E I J e.val).mp e.property).2.2 ∈
        (bipartiteDecode E ⟨I, J, S⟩).val ↔ e ∉ S := by
  change (¬ ∃ h, ⟨(e.val.1, e.val.2), h⟩ ∈ S) ↔ e ∉ S
  constructor
  · intro hn hs
    exact hn ⟨e.property, hs⟩
  · rintro hn ⟨h, hs⟩
    exact hn hs

theorem bipartiteDecode_injective : Function.Injective (bipartiteDecode E) := by
  rintro ⟨I, J, S⟩ ⟨I', J', S'⟩ h
  have hI : I = I' := by
    ext l
    have hv := congrArg (fun W : BipartiteUpsets E => bipartiteLeftDiagonalInterval E l ∈ W.val) h
    exact not_iff_not.mp (by simpa only [bipartiteDecode_left] using eq_iff_iff.mp hv)
  have hJ : J = J' := by
    ext r
    have hv := congrArg (fun W : BipartiteUpsets E => bipartiteRightDiagonalInterval E r ∈ W.val) h
    exact not_iff_not.mp (by simpa only [bipartiteDecode_right] using eq_iff_iff.mp hv)
  subst I'
  subst J'
  have hS : S = S' := by
    ext e
    have hv := congrArg (fun W : BipartiteUpsets E =>
      bipartiteEdgeInterval E e.val.1 e.val.2
        ((mem_bipartiteFreeEdges E I J e.val).mp e.property).2.2 ∈ W.val) h
    exact not_iff_not.mp (by simpa only [bipartiteDecode_free_edge] using eq_iff_iff.mp hv)
  subst S'
  rfl

variable [Fintype L] [Fintype R]

def bipartiteMissingLeft (W : BipartiteUpsets E) : Finset L :=
  Finset.univ.filter (fun l => bipartiteLeftDiagonalInterval E l ∉ W.val)

def bipartiteMissingRight (W : BipartiteUpsets E) : Finset R :=
  Finset.univ.filter (fun r => bipartiteRightDiagonalInterval E r ∉ W.val)

omit [Fintype R] in
@[simp] theorem mem_bipartiteMissingLeft (W : BipartiteUpsets E) (l : L) :
    l ∈ bipartiteMissingLeft E W ↔ bipartiteLeftDiagonalInterval E l ∉ W.val := by
  simp [bipartiteMissingLeft]

omit [Fintype L] in
@[simp] theorem mem_bipartiteMissingRight (W : BipartiteUpsets E) (r : R) :
    r ∈ bipartiteMissingRight E W ↔ bipartiteRightDiagonalInterval E r ∉ W.val := by
  simp [bipartiteMissingRight]

def bipartiteEncode (W : BipartiteUpsets E) : BipartiteChoices E :=
  ⟨bipartiteMissingLeft E W, bipartiteMissingRight E W,
    {e | bipartiteEdgeInterval E e.val.1 e.val.2
      ((mem_bipartiteFreeEdges E _ _ e.val).mp e.property).2.2 ∉ W.val}⟩

omit [Fintype L] [Fintype R] in
theorem bipartite_missing_edge_endpoints (W : BipartiteUpsets E)
    (l : L) (r : R) (he : E l r) (hw : bipartiteEdgeInterval E l r he ∉ W.val) :
    bipartiteLeftDiagonalInterval E l ∉ W.val ∧ bipartiteRightDiagonalInterval E r ∉ W.val := by
  constructor
  · intro hl
    exact hw (W.property (bipartiteLeftDiagonalInterval E l) hl
      (bipartiteEdgeInterval E l r he) rfl he)
  · intro hr
    exact hw (W.property (bipartiteRightDiagonalInterval E r) hr
      (bipartiteEdgeInterval E l r he) he rfl)

theorem bipartiteDecode_encode (W : BipartiteUpsets E) :
    bipartiteDecode E (bipartiteEncode E W) = W := by
  apply Subtype.ext
  apply Set.ext
  rintro ⟨⟨a, b⟩, hab⟩
  cases a with
  | inl l =>
    cases b with
    | inl l' =>
      have heq : l = l' := hab
      subst l'
      change (bipartiteLeftDiagonalInterval E l ∈
        (bipartiteDecode E (bipartiteEncode E W)).val) ↔ _
      simp [bipartiteEncode]
      rfl
    | inr r =>
      change (¬ ∃ h : (l, r) ∈ bipartiteFreeEdges E
        (bipartiteMissingLeft E W) (bipartiteMissingRight E W),
          bipartiteEdgeInterval E l r hab ∉ W.val) ↔
            bipartiteEdgeInterval E l r hab ∈ W.val
      constructor
      · intro hn
        by_contra hw
        obtain ⟨hl, hr⟩ := bipartite_missing_edge_endpoints E W l r hab hw
        have hm : (l, r) ∈ bipartiteFreeEdges E
            (bipartiteMissingLeft E W) (bipartiteMissingRight E W) := by
          simp only [mem_bipartiteFreeEdges, mem_bipartiteMissingLeft,
            mem_bipartiteMissingRight]
          exact ⟨hl, hr, hab⟩
        exact hn ⟨hm, hw⟩
      · rintro hw ⟨_, hn⟩
        exact hn hw
  | inr r =>
    cases b with
    | inl l => exact False.elim hab
    | inr r' =>
      have heq : r = r' := hab
      subst r'
      change (bipartiteRightDiagonalInterval E r ∈
        (bipartiteDecode E (bipartiteEncode E W)).val) ↔ _
      simp [bipartiteEncode]
      rfl

/-- An upset is determined by its missing diagonal intervals and its missing free edges. -/
def bipartiteUpsetsEquivChoices : BipartiteUpsets E ≃ BipartiteChoices E :=
  (Equiv.ofBijective (bipartiteDecode E)
    ⟨bipartiteDecode_injective E, fun W => ⟨bipartiteEncode E W, bipartiteDecode_encode E W⟩⟩).symm

/-- Proposition 8.5: the exact finite bipartite interval-upset enumeration. -/
theorem proposition_8_5_proof : Proposition_8_5 L R E := by
  change Nat.card (BipartiteUpsets E) = _
  rw [Nat.card_congr (bipartiteUpsetsEquivChoices E)]
  unfold BipartiteChoices
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro I _
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro J _
  rw [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_coe]
  rfl

end Posets

