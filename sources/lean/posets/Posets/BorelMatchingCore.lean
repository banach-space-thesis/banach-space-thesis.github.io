import Mathlib.Topology.Bases
import Mathlib.Data.Set.Countable

/-! Prune a countable union of small open sets. The resulting closed core
has no nonempty relatively open small subset. This is independent of the
particular countable-coordinate-cover ideal used for Borel matching. -/

noncomputable section
open Set TopologicalSpace
namespace Posets

theorem exists_closed_core_of_not_small {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (small : Set X → Prop)
    (hmono : ∀ {s t : Set X}, s ⊆ t → small t → small s)
    (hunion : ∀ S : Set (Set X), S.Countable →
      (∀ s ∈ S, small s) → small (⋃₀ S)) (hnot : ¬ small univ) :
    ∃ C : Set X, IsClosed C ∧ C.Nonempty ∧
      ∀ U : Set X, IsOpen U → (C ∩ U).Nonempty → ¬ small (C ∩ U) := by
  classical
  let S : Set (Set X) := {U | IsOpen U ∧ small U}
  let V : Set X := ⋃₀ S
  have hVo : IsOpen V := isOpen_sUnion (fun U hU => hU.1)
  obtain ⟨T, hTc, hTS, hTV⟩ := isOpen_sUnion_countable S (fun U hU => hU.1)
  have hVs : small V := by
    rw [show V = ⋃₀ T from hTV.symm]
    exact hunion T hTc (fun U hU => (hTS hU).2)
  have hCn : (Vᶜ).Nonempty := by
    by_contra hn
    have he : Vᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have heV : V = univ := by simpa using congrArg (fun W : Set X => Wᶜ) he
    exact hnot (heV ▸ hVs)
  refine ⟨Vᶜ, hVo.isClosed_compl, hCn, ?_⟩
  intro U hU hmeet hsmall
  have hsum : small (V ∪ (Vᶜ ∩ U)) := by
    have h := hunion {V, Vᶜ ∩ U} ((Set.finite_singleton _).insert _).countable (by
      intro W hW
      rcases Set.mem_insert_iff.mp hW with rfl | hW
      · exact hVs
      · exact Set.mem_singleton_iff.mp hW ▸ hsmall)
    simpa only [Set.sUnion_pair] using h
  have hUs : small U := hmono (by
    intro x hx
    by_cases h : x ∈ V
    · exact Or.inl h
    · exact Or.inr ⟨h, hx⟩) hsum
  have hUV : U ⊆ V := Set.subset_sUnion_of_mem (show U ∈ S from ⟨hU, hUs⟩)
  obtain ⟨x, hxC, hxU⟩ := hmeet
  exact hxC (hUV hxU)

end Posets
