import Posets.SupportingStatements
import ThesisCommon.Analysis.AlmostDisjointFamily

/-! The binary-tree family has a closed characteristic-function image in Cantor space. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open ThesisCommon Cardinal
namespace Posets

theorem treeBranchSet_injective : Function.Injective branchSet := by
  intro f g h
  by_contra hfg
  have hfin := branchSet_inter_finite hfg
  rw [← h, Set.inter_self] at hfin
  exact branchSet_infinite f hfin

/-- Membership of a finite tree node depends on only a finite prefix of the branch. -/
theorem continuous_cantorCode_branchSet : Continuous (fun f : ℕ → Bool => cantorCode (branchSet f)) := by
  apply continuous_pi
  intro n
  by_cases hn : ∃ l : List Bool, Encodable.encode l = n
  · obtain ⟨l, rfl⟩ := hn
    have hmem (f : ℕ → Bool) : Encodable.encode l ∈ branchSet f ↔
        List.ofFn (fun i : Fin l.length => f i.val) = l := by
      constructor
      · rintro ⟨m, hm⟩
        have he : List.ofFn (fun i : Fin m => f i.val) = l := Encodable.encode_injective hm
        have hlen : m = l.length := by simpa only [List.length_ofFn] using congrArg List.length he
        subst m
        exact he
      · intro he
        exact ⟨l.length, by change Encodable.encode _ = _; rw [he]⟩
    have hprefix : Continuous (fun f : ℕ → Bool => fun i : Fin l.length => f i.val) :=
      continuous_pi (fun i => continuous_apply i.val)
    have htest : Continuous (fun v : Fin l.length → Bool => decide (List.ofFn v = l)) :=
      continuous_of_discreteTopology
    simpa only [Function.comp_def, cantorCode, hmem] using htest.comp hprefix
  · have heq : (fun f : ℕ → Bool => cantorCode (branchSet f) n) = fun _ => false := by
      funext f
      apply decide_eq_false
      rintro ⟨m, hm⟩
      exact hn ⟨List.ofFn (fun i : Fin m => f i.val), hm⟩
    rw [heq]
    exact continuous_const

def closedTreeFamily : Set (Set ℕ) := Set.range branchSet

theorem closedTreeFamily_almostDisjoint : IsAlmostDisjoint closedTreeFamily := by
  constructor
  · rintro _ ⟨f, rfl⟩
    exact branchSet_infinite f
  · rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ hne
    exact branchSet_inter_finite (fun h => hne (congrArg branchSet h))

theorem closedTreeFamily_card : #closedTreeFamily = 𝔠 := by
  rw [closedTreeFamily, Cardinal.mk_range_eq branchSet treeBranchSet_injective]
  simp only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id]
  rfl

theorem closedTreeFamily_uncountable : ¬ closedTreeFamily.Countable := by
  intro hc
  have hle := Cardinal.le_aleph0_iff_set_countable.mpr hc
  rw [closedTreeFamily_card] at hle
  exact Cardinal.aleph0_lt_continuum.not_ge hle

theorem closedTreeFamily_cantorCode_closed : IsClosed (cantorCode '' closedTreeFamily) := by
  have heq : cantorCode '' closedTreeFamily = Set.range (fun f : ℕ → Bool => cantorCode (branchSet f)) :=
    by
      ext y
      constructor
      · rintro ⟨A, ⟨f, rfl⟩, rfl⟩
        exact ⟨f, rfl⟩
      · rintro ⟨f, rfl⟩
        exact ⟨branchSet f, ⟨f, rfl⟩, rfl⟩
  rw [heq]
  exact (isCompact_range continuous_cantorCode_branchSet).isClosed

/-- Lemma 5.1, with the closed Cantor-space image required by the paper. -/
theorem lemma_5_1_proof : Lemma_5_1 :=
  ⟨closedTreeFamily, closedTreeFamily_almostDisjoint, closedTreeFamily_uncountable,
    closedTreeFamily_cantorCode_closed⟩

end Posets
