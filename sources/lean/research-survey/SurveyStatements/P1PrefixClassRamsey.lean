import SurveyStatements.P1ClosedRamsey

/-! Closed Ramsey for classes of infinite increasing sequences. Closedness is
expressed directly by a finite initial-prefix certificate for nonmembership,
which is the form used by continuous finite witnesses in Elton selection. -/

noncomputable section
set_option autoImplicit false
open Set

namespace SurveyStatements.P1

theorem strictMono_prefix_card (ν : ℕ → ℕ) (hν : StrictMono ν) (N : ℕ) :
    ((Finset.range N).image ν).card = N := by
  rw [Finset.card_image_of_injective _ hν.injective, Finset.card_range]

theorem prefixClass_closedRamsey
    (C : Set ℕ → Prop)
    (hclosed : ∀ ν : ℕ → ℕ, StrictMono ν → ¬ C (range ν) →
      ∃ N : ℕ, ∀ η : ℕ → ℕ, StrictMono η →
        (Finset.range N).image η = (Finset.range N).image ν → ¬ C (range η))
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ((∀ ν : ℕ → ℕ, StrictMono ν → range ν ⊆ L → C (range ν)) ∨
       (∀ ν : ℕ → ℕ, StrictMono ν → range ν ⊆ L → ¬ C (range ν))) := by
  classical
  by_cases hbranches : ∀ N : Set ℕ, N ⊆ M → N.Infinite →
      ∃ ν : ℕ → ℕ, StrictMono ν ∧ range ν ⊆ N ∧ C (range ν)
  · let P : Finset ℕ → Prop := fun s => ∃ ν : ℕ → ℕ,
      StrictMono ν ∧ (Finset.range s.card).image ν = s ∧ C (range ν)
    have hbranchP : ∀ N : Set ℕ, N ⊆ M → N.Infinite →
        ∃ ν : ℕ → ℕ, StrictMono ν ∧ (∀ n, ν n ∈ N) ∧
          ∀ n, P ((Finset.range n).image ν) := by
      intro N hNM hN
      obtain ⟨ν, hν, hνN, hC⟩ := hbranches N hNM hN
      refine ⟨ν, hν, fun n => hνN ⟨n, rfl⟩, ?_⟩
      intro n
      refine ⟨ν, hν, ?_, hC⟩
      rw [strictMono_prefix_card ν hν n]
    obtain ⟨L, hLM, hL, hP⟩ := closedRamsey_from_infinite_branches P M hM hbranchP
    refine ⟨L, hLM, hL, Or.inl ?_⟩
    intro ν hν hνL
    by_contra hC
    obtain ⟨N, hN⟩ := hclosed ν hν hC
    have hp : P ((Finset.range N).image ν) := hP _ (by
      intro n hn
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
      exact hνL ⟨i, rfl⟩)
    obtain ⟨η, hη, hfront, hηC⟩ := hp
    rw [strictMono_prefix_card ν hν N] at hfront
    exact hN η hη hfront hηC
  · push_neg at hbranches
    obtain ⟨L, hLM, hL, hnone⟩ := hbranches
    refine ⟨L, hLM, hL, Or.inr ?_⟩
    intro ν hν hνL
    exact hnone ν hν hνL

theorem prefixClass_finiteColorRamsey {α : Type*} [Finite α]
    (F : Set ℕ → α)
    (hlocal : ∀ ν : ℕ → ℕ, StrictMono ν → ∃ N : ℕ,
      ∀ η : ℕ → ℕ, StrictMono η →
        (Finset.range N).image η = (Finset.range N).image ν → F (range η) = F (range ν))
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧ ∃ a : α,
      ∀ ν : ℕ → ℕ, StrictMono ν → range ν ⊆ L → F (range ν) = a := by
  classical
  letI := Fintype.ofFinite α
  have hfinite : ∀ S : Finset α, ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ a ∈ S,
        (∀ ν : ℕ → ℕ, StrictMono ν → range ν ⊆ L → F (range ν) = a) ∨
        (∀ ν : ℕ → ℕ, StrictMono ν → range ν ⊆ L → F (range ν) ≠ a) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨M, subset_rfl, hM, by simp⟩
    | @insert a S ha ih =>
      obtain ⟨N, hNM, hN, hdec⟩ := ih
      have hclosed : ∀ ν : ℕ → ℕ, StrictMono ν → F (range ν) ≠ a →
          ∃ K : ℕ, ∀ η : ℕ → ℕ, StrictMono η →
            (Finset.range K).image η = (Finset.range K).image ν → F (range η) ≠ a := by
        intro ν hν hne
        obtain ⟨K, hK⟩ := hlocal ν hν
        refine ⟨K, ?_⟩
        intro η hη heq
        rw [hK η hη heq]
        exact hne
      obtain ⟨L, hLN, hL, hcolor⟩ := prefixClass_closedRamsey (fun A => F A = a) hclosed N hN
      refine ⟨L, hLN.trans hNM, hL, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hcolor
      · rcases hdec b hb with h | h
        · exact Or.inl (fun ν hν hνL => h ν hν (hνL.trans hLN))
        · exact Or.inr (fun ν hν hνL => h ν hν (hνL.trans hLN))
  obtain ⟨L, hLM, hL, hdec⟩ := hfinite Finset.univ
  obtain ⟨ν, hν, hνL⟩ := infiniteSet_exists_strictMono_sequence L hL
  let a := F (range ν)
  refine ⟨L, hLM, hL, a, ?_⟩
  rcases hdec a (Finset.mem_univ a) with h | h
  · exact h
  · exact False.elim (h ν hν (by rintro _ ⟨n, rfl⟩; exact hνL n) rfl)

end SurveyStatements.P1
