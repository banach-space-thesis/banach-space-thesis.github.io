import SurveyStatements.P1FiniteWitnessSelection
import SurveyStatements.P1ThinFamilyRamseyFinite

/-! Preferred finite-support witnesses. The whole witness is locally constant,
and minimizing its support height makes the selected support family thin. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

theorem exists_preferred_support_selection {Ω : Type*} (supp : Ω → Finset ℕ)
    (hne : ∀ ω, (supp ω).Nonempty)
    (hex : ∀ M : Set ℕ, M.Infinite → ∃ ω : Ω, (supp ω : Set ℕ) ⊆ M) :
    ∃ φ : Set ℕ → Ω,
      (∀ M, M.Infinite → (supp (φ M) : Set ℕ) ⊆ M) ∧
      (∀ M, M.Infinite → ∃ r : ℕ, ∀ N, N.Infinite →
        (∀ i : ℕ, i < r → (i ∈ M ↔ i ∈ N)) → φ N = φ M) ∧
      (∀ M N, M.Infinite → N.Infinite →
        (supp (φ N) : Set ℕ) ⊆ M → (supp (φ M) : Set ℕ) ⊆ N → φ N = φ M) ∧
      IsThinFiniteFamily {s | ∃ M : Set ℕ, M.Infinite ∧ s = supp (φ M)} := by
  let height (ω : Ω) := (supp ω).sup id
  obtain ⟨ψ, hvalid, hmutual, hminimal, hlocal⟩ :=
    exists_preferred_locally_constant_finiteWitness_selection height
      (fun M ω => (supp ω : Set ℕ) ⊆ M) hex
  let φ (M : Set ℕ) : Ω := if hM : M.Infinite then ψ M hM else ψ univ Set.infinite_univ
  have hφ (M : Set ℕ) (hM : M.Infinite) : φ M = ψ M hM := dif_pos hM
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro M hM
    rw [hφ M hM]
    exact hvalid M hM
  · intro M hM
    refine ⟨height (ψ M hM) + 1, ?_⟩
    intro N hN hagree
    rw [hφ N hN, hφ M hM]
    apply hlocal M N hM hN
    intro ω hheight
    constructor
    · intro hω i hi
      exact (hagree i (by
        have hi' : i ≤ height ω := Finset.le_sup (f := id) hi
        omega)).mp (hω hi)
    · intro hω i hi
      exact (hagree i (by
        have hi' : i ≤ height ω := Finset.le_sup (f := id) hi
        omega)).mpr (hω hi)
  · intro M N hM hN hNM hMN
    simp only [hφ N hN, hφ M hM] at hNM hMN ⊢
    exact hmutual M N hM hN hNM hMN
  · rintro s ⟨M, hM, rfl⟩ t ⟨N, hN, rfl⟩ hst
    rw [hφ M hM, hφ N hN] at hst ⊢
    have hsN : (supp (ψ M hM) : Set ℕ) ⊆ N :=
      fun i hi => hvalid N hN (hst.1 hi)
    have hheight : height (ψ N hN) ≤ height (ψ M hM) :=
      hminimal N hN (ψ M hM) hsN
    apply Finset.Subset.antisymm hst.1
    intro b hb
    by_contra hbs
    have hmaxmem : (supp (ψ M hM)).sup id ∈ supp (ψ M hM) := by
      simpa using Finset.sup_mem_of_nonempty (f := id) (hne (ψ M hM))
    have hmaxlt : height (ψ M hM) < b := hst.2 _ hmaxmem b hb hbs
    have hbmax : b ≤ height (ψ N hN) := Finset.le_sup (f := id) hb
    omega

end SurveyStatements.P1
