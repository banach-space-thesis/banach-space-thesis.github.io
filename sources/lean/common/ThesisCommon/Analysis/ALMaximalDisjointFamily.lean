import ThesisCommon.Analysis.ALRefinementPrincipal
import Mathlib.Order.Zorn

/-! A maximal disjoint family of nonzero positive vectors, and orthogonality
of its principal bands. No atomicity or representation is assumed. -/
noncomputable section
open Set
namespace ThesisCommon
section General
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

omit [IsOrderedAddMonoid E] in
theorem exists_total_positive_disjoint_family :
    ∃ S : Set E, (∀ e ∈ S, 0 ≤ e ∧ e ≠ 0) ∧
      S.Pairwise (fun e f => e ⊓ f = 0) ∧
      ∀ x : E, 0 ≤ x → (∀ e ∈ S, x ⊓ e = 0) → x = 0 := by
  let A : Set (Set E) := {S | (∀ e ∈ S, 0 ≤ e ∧ e ≠ 0) ∧
    S.Pairwise (fun e f => e ⊓ f = 0)}
  obtain ⟨S, hS⟩ := zorn_subset A (by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
    · rintro e ⟨s, hs, he⟩
      exact (hc hs).1 e he
    · rintro e ⟨s, hs, he⟩ f ⟨t, ht, hf⟩ hef
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 (hst he) hf hef
      · exact (hc hs).2 he (hts hf) hef)
  refine ⟨S, hS.prop.1, hS.prop.2, ?_⟩
  intro x hx hdis
  by_contra hx0
  have hi : insert x S ∈ A := by
    refine ⟨?_, ?_⟩
    · intro e he
      rcases mem_insert_iff.mp he with rfl | he
      · exact ⟨hx, hx0⟩
      · exact hS.prop.1 e he
    · intro e he f hf hef
      rcases mem_insert_iff.mp he with hex | heS
      · subst e
        rcases mem_insert_iff.mp hf with hfx | hfS
        · exact (hef hfx.symm).elim
        · exact hdis f hfS
      · rcases mem_insert_iff.mp hf with hfx | hfS
        · subst f
          rw [inf_comm]
          exact hdis e heS
        · exact hS.prop.2 heS hfS hef
  have heq : insert x S = S := (hS.eq_of_subset hi (subset_insert x S)).symm
  have hxs : x ∈ S := heq ▸ mem_insert x S
  have hh := hdis x hxs
  rw [inf_idem] at hh
  exact hx0 hh

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ConditionallyCompleteLattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem principalBand_disjoint_of_disjoint {a b x y : E}
    (hab : |a| ⊓ |b| = 0) (hx : x ∈ principalBand a) (hy : y ∈ principalBand b) :
    |x| ⊓ |y| = 0 := by
  have ha : a ∈ latticeDisjointComplement ({b} : Set E) := by
    intro z hz
    simpa only [Set.mem_singleton_iff.mp hz] using hab
  apply hx y
  intro z hz
  simpa only [Set.mem_singleton_iff.mp hz] using hy a ha

theorem principalBandProjection_orthogonal {a b : E}
    (hab : |a| ⊓ |b| = 0) (x : E) :
    principalBandProjection a (principalBandProjection b x) = 0 := by
  apply (principalBandProjection_eq_zero_iff a _).mpr
  rw [inf_comm]
  exact principalBand_disjoint_of_disjoint hab (self_mem_principalBand a)
    ((principalBand_orderClosed b).bandProjection_mem x)

end ThesisCommon
