import SurveyStatements.P1FiniteInitialSegments

/-! The finite-color Nash-Williams theorem for actual thin families. The proof
uses the checked closed-prefix Ramsey theorem and extends every finite support
to an increasing infinite branch. No barrier-cover assumption is introduced. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

def IsThinFiniteFamily (A : Set (Finset ℕ)) : Prop :=
  ∀ s ∈ A, ∀ t ∈ A, FinsetIsInitialSegment s t → s = t

theorem thin_family_prefix_unique (A : Set (Finset ℕ)) (hA : IsThinFiniteFamily A)
    (ν : ℕ → ℕ) (hν : StrictMono ν) (s t : Finset ℕ)
    (hs : s ∈ A) (ht : t ∈ A)
    (hsp : FinsetIsInitialSegmentOfSet s (range ν))
    (htp : FinsetIsInitialSegmentOfSet t (range ν)) : s = t := by
  rcases initialSegmentsOfSet_comparable ν hν s t hsp htp with h | h
  · exact hA s hs t ht h
  · exact (hA t ht s hs h).symm

theorem thin_family_color_dichotomy {α : Type*} (A : Set (Finset ℕ))
    (hA : IsThinFiniteFamily A) (c : Finset ℕ → α) (a : α)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ((∀ s ∈ A, (s : Set ℕ) ⊆ L → c s ≠ a) ∨
       (∀ s ∈ A, (s : Set ℕ) ⊆ L → c s = a)) := by
  let C : Set ℕ → Prop := fun N =>
    ¬ ∃ s ∈ A, FinsetIsInitialSegmentOfSet s N ∧ c s = a
  have hclosed : ∀ ν : ℕ → ℕ, StrictMono ν → ¬ C (range ν) →
      ∃ n, ∀ η : ℕ → ℕ, StrictMono η →
        (Finset.range n).image η = (Finset.range n).image ν → ¬ C (range η) := by
    intro ν hν hC
    obtain ⟨s, hs, hsp, hcs⟩ : ∃ s ∈ A,
        FinsetIsInitialSegmentOfSet s (range ν) ∧ c s = a := Classical.not_not.mp hC
    obtain ⟨n, hn⟩ := initialSegmentOfSet_eq_prefix ν hν s hsp
    refine ⟨n, ?_⟩
    intro η hη heq hCη
    apply hCη
    refine ⟨s, hs, ?_, hcs⟩
    have hp := strictMono_prefix_initialSegmentOfSet η hη n
    rw [heq, hn] at hp
    exact hp
  obtain ⟨L, hLM, hL, hdec⟩ := prefixClass_closedRamsey C hclosed M hM
  refine ⟨L, hLM, hL, ?_⟩
  rcases hdec with h | h
  · left
    intro s hs hsL hcs
    obtain ⟨ν, hν, hνL, hsp⟩ := infinite_branch_extending_finset L hL s hsL
    exact h ν hν hνL ⟨s, hs, hsp, hcs⟩
  · right
    intro s hs hsL
    obtain ⟨ν, hν, hνL, hsp⟩ := infinite_branch_extending_finset L hL s hsL
    obtain ⟨t, ht, htp, hct⟩ : ∃ t ∈ A,
        FinsetIsInitialSegmentOfSet t (range ν) ∧ c t = a :=
      Classical.not_not.mp (h ν hν hνL)
    have hst := thin_family_prefix_unique A hA ν hν s t hs ht hsp htp
    simpa only [hst] using hct

theorem thin_family_finiteColorRamsey {α : Type*} [Finite α]
    (A : Set (Finset ℕ)) (hA : IsThinFiniteFamily A) (c : Finset ℕ → α)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ s ∈ A, ∀ t ∈ A, (s : Set ℕ) ⊆ L → (t : Set ℕ) ⊆ L → c s = c t := by
  letI := Fintype.ofFinite α
  have hdec : ∀ S : Finset α, ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ a ∈ S, (∀ s ∈ A, (s : Set ℕ) ⊆ L → c s ≠ a) ∨
        (∀ s ∈ A, (s : Set ℕ) ⊆ L → c s = a) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨M, subset_rfl, hM, by simp⟩
    | @insert a S ha ih =>
      obtain ⟨N, hNM, hN, hNdec⟩ := ih
      obtain ⟨L, hLN, hL, hcolor⟩ := thin_family_color_dichotomy A hA c a N hN
      refine ⟨L, hLN.trans hNM, hL, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hcolor
      · rcases hNdec b hb with h | h
        · exact Or.inl (fun s hs hsL => h s hs (hsL.trans hLN))
        · exact Or.inr (fun s hs hsL => h s hs (hsL.trans hLN))
  obtain ⟨L, hLM, hL, hcolor⟩ := hdec Finset.univ
  refine ⟨L, hLM, hL, ?_⟩
  intro s hs t ht hsL htL
  rcases hcolor (c s) (Finset.mem_univ _) with h | h
  · exact (h s hs hsL rfl).elim
  · exact (h t ht htL).symm

end SurveyStatements.P1
