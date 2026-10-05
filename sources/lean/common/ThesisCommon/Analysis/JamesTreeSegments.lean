import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic

/-! Two explicit segment conventions on the full dyadic tree. Nodes are
finite binary words; the predecessor relation is the prefix relation.
The literal manuscript allows finite chains with gaps. The consecutive
convention additionally includes every intermediate prefix. No unqualified
JT space or identification between these conventions is chosen here. -/
noncomputable section
namespace ThesisCommon

/-- Binary words model the full rooted dyadic tree. -/
abbrev DyadicTreeNode := List Bool

/-- The manuscript's literal nonempty finite-chain convention. -/
def IsLiteralTreeSegment (A : Finset DyadicTreeNode) : Prop :=
  A.Nonempty ∧ ∀ s ∈ A, ∀ t ∈ A, s.IsPrefix t ∨ t.IsPrefix s

/-- The consecutive convention: a chain containing all intermediate nodes. -/
def IsConsecutiveTreeSegment (A : Finset DyadicTreeNode) : Prop :=
  IsLiteralTreeSegment A ∧
    ∀ s ∈ A, ∀ t ∈ A, ∀ u, s.IsPrefix u → u.IsPrefix t → u ∈ A

theorem literalTreeSegment_singleton (t : DyadicTreeNode) :
    IsLiteralTreeSegment {t} := by
  refine ⟨Finset.singleton_nonempty t, ?_⟩
  intro s hs u hu
  simp only [Finset.mem_singleton] at hs hu
  subst s
  subst u
  exact Or.inl List.prefix_rfl

theorem consecutiveTreeSegment_singleton (t : DyadicTreeNode) :
    IsConsecutiveTreeSegment {t} := by
  refine ⟨literalTreeSegment_singleton t, ?_⟩
  intro s hs v hv u hsu huv
  simp only [Finset.mem_singleton] at hs hv ⊢
  subst s
  subst v
  exact huv.eq_of_length (huv.length_le.antisymm hsu.length_le)

/-- Only the singleton law is required to make the resulting norm definite. -/
structure JamesTreeSegmentFamily where
  allows : Finset DyadicTreeNode → Prop
  singleton_allowed : ∀ t, allows {t}

def literalTreeSegmentFamily : JamesTreeSegmentFamily where
  allows := IsLiteralTreeSegment
  singleton_allowed := literalTreeSegment_singleton

def consecutiveTreeSegmentFamily : JamesTreeSegmentFamily where
  allows := IsConsecutiveTreeSegment
  singleton_allowed := consecutiveTreeSegment_singleton

theorem consecutiveTreeSegment_isLiteral {A : Finset DyadicTreeNode}
    (h : IsConsecutiveTreeSegment A) : IsLiteralTreeSegment A := h.1

/-- A checked witness that the two segment conventions differ. -/
theorem treeSegment_conventions_distinct :
    IsLiteralTreeSegment {[], [false, false]} ∧
      ¬ IsConsecutiveTreeSegment {[], [false, false]} := by
  constructor
  · refine ⟨by simp, ?_⟩
    intro s hs t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp
  · intro h
    have hm := h.2 [] (by simp) [false, false] (by simp) [false]
      (by simp) (show ([false] : List Bool).IsPrefix [false, false] from ⟨[false], rfl⟩)
    simp at hm

/-- A finite family of pairwise disjoint allowed segments. -/
structure JamesTreeTest (S : JamesTreeSegmentFamily) where
  count : ℕ
  segment : Fin count → Finset DyadicTreeNode
  allowed : ∀ j, S.allows (segment j)
  disjoint : Pairwise (fun i j => Disjoint (segment i) (segment j))

def JamesTreeTest.singleton (S : JamesTreeSegmentFamily) (t : DyadicTreeNode) :
    JamesTreeTest S where
  count := 1
  segment _ := {t}
  allowed _ := S.singleton_allowed t
  disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim

instance (S : JamesTreeSegmentFamily) : Nonempty (JamesTreeTest S) :=
  ⟨JamesTreeTest.singleton S []⟩

end ThesisCommon
