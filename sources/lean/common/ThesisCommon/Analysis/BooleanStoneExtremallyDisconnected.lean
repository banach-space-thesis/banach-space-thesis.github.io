import ThesisCommon.Analysis.BooleanStoneSeparation
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Order.CompleteBooleanAlgebra

/-! The Stone clopens form a basis, and a complete Boolean algebra has
an extremally disconnected Stone space. Arbitrary index sets and the
trivial Boolean algebra are allowed. -/
noncomputable section
open Set TopologicalSpace
namespace ThesisCommon
section Boolean
variable {B : Type*} [BooleanAlgebra B]

theorem exists_booleanStoneSet_separating_points
    (p q : BooleanStonePoint B) (hpq : p ≠ q) :
    ∃ a : B, p ∈ booleanStoneSet a ∧ q ∉ booleanStoneSet a := by
  have hval : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hval
  change booleanStoneHom p a ≠ booleanStoneHom q a at ha
  cases hpa : booleanStoneHom p a <;> cases hqa : booleanStoneHom q a
  · exact False.elim (ha (hpa.trans hqa.symm))
  · refine ⟨aᶜ, ?_, ?_⟩ <;> simp [booleanStoneSet, map_compl', hpa, hqa]
  · exact ⟨a, hpa, by simp [booleanStoneSet, hqa]⟩
  · exact False.elim (ha (hpa.trans hqa.symm))

theorem booleanStoneSet_finset_inf {ι : Type*} (s : Finset ι) (a : ι → B) :
    booleanStoneSet (s.inf a) = ⋂ i ∈ s, booleanStoneSet (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.inf_insert, ih]

theorem booleanStoneSet_finset_sup {ι : Type*} (s : Finset ι) (a : ι → B) :
    booleanStoneSet (s.sup a) = ⋃ i ∈ s, booleanStoneSet (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sup_insert, ih]

theorem isTopologicalBasis_range_booleanStoneSet :
    IsTopologicalBasis (range (booleanStoneSet (B := B))) := by
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact (isClopen_booleanStoneSet a).isOpen
  · intro p U hp hU
    have hsep (q : {q : BooleanStonePoint B // q ∉ U}) :
        ∃ a : B, p ∈ booleanStoneSet a ∧ q.val ∉ booleanStoneSet a :=
      exists_booleanStoneSet_separating_points p q.val (by
        intro h
        exact q.property (h ▸ hp))
    choose a ha using hsep
    obtain ⟨s, hs⟩ := hU.isClosed_compl.isCompact.elim_finite_subcover
      (fun q : {q : BooleanStonePoint B // q ∉ U} => (booleanStoneSet (a q))ᶜ)
      (fun q => (isClopen_booleanStoneSet (a q)).isClosed.isOpen_compl)
      (by
        intro q hq
        exact mem_iUnion.mpr ⟨⟨q, hq⟩, (ha ⟨q, hq⟩).2⟩)
    refine ⟨booleanStoneSet (s.inf a), ⟨s.inf a, rfl⟩, ?_, ?_⟩
    · rw [booleanStoneSet_finset_inf]
      exact mem_iInter₂.mpr (fun q _ => (ha q).1)
    · intro q hq
      by_contra hqU
      obtain ⟨j, hjs, hjq⟩ := mem_iUnion₂.mp (hs hqU)
      rw [booleanStoneSet_finset_inf] at hq
      exact hjq (mem_iInter₂.mp hq j hjs)

theorem isOpen_eq_iUnion_booleanStoneSet {U : Set (BooleanStonePoint B)} (hU : IsOpen U) :
    U = ⋃ a : {a : B // booleanStoneSet a ⊆ U}, booleanStoneSet a.val := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, ⟨a, rfl⟩, hpa, ha⟩ :=
      isTopologicalBasis_range_booleanStoneSet.mem_nhds_iff.mp (hU.mem_nhds hp)
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, hpa⟩
  · intro hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp hp
    exact a.property ha

theorem exists_booleanStoneSet_eq_of_isClopen
    {U : Set (BooleanStonePoint B)} (hU : IsClopen U) :
    ∃ a : B, booleanStoneSet a = U := by
  classical
  obtain ⟨s, hs, heq⟩ := eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
    booleanStoneSet isTopologicalBasis_range_booleanStoneSet U hU.isClosed.isCompact hU.isOpen
  refine ⟨hs.toFinset.sup id, ?_⟩
  rw [booleanStoneSet_finset_sup]
  simpa using heq.symm

end Boolean

section Complete
variable {B : Type*} [CompleteBooleanAlgebra B]

theorem closure_iUnion_booleanStoneSet {ι : Type*} (a : ι → B) :
    closure (⋃ i, booleanStoneSet (a i)) = booleanStoneSet (⨆ i, a i) := by
  apply le_antisymm
  · apply closure_minimal
    · exact iUnion_subset (fun i => (booleanStoneSet_subset_iff _ _).mpr (le_iSup a i))
    · exact (isClopen_booleanStoneSet _).isClosed
  · intro p hp
    rw [isTopologicalBasis_range_booleanStoneSet.mem_closure_iff]
    rintro _ ⟨b, rfl⟩ hb
    have hnot : b ⊓ (⨆ i, a i) ≠ ⊥ :=
      (booleanStoneSet_nonempty_iff _).mp ⟨p, by rw [booleanStoneSet_inf]; exact ⟨hb, hp⟩⟩
    have hex : ∃ i, b ⊓ a i ≠ ⊥ := by
      by_contra h
      push_neg at h
      apply hnot
      rw [inf_iSup_eq]
      simp [h]
    obtain ⟨i, hi⟩ := hex
    obtain ⟨q, hq⟩ := (booleanStoneSet_nonempty_iff _).mpr hi
    rw [booleanStoneSet_inf] at hq
    exact ⟨q, hq.1, mem_iUnion.mpr ⟨i, hq.2⟩⟩

instance booleanStonePointExtremallyDisconnected : ExtremallyDisconnected (BooleanStonePoint B) where
  open_closure U hU := by
    rw [isOpen_eq_iUnion_booleanStoneSet hU, closure_iUnion_booleanStoneSet]
    exact (isClopen_booleanStoneSet _).isOpen

end Complete
end ThesisCommon
