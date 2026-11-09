import SurveyStatements.P1PrefixClassRamsey
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.WellFounded

/-! Continuous selection of finite witnesses, in finite-height form.
The selector first minimizes the natural-number support height and then
uses one fixed well-order on the bounded-height witness set. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

private theorem witnessHeight_exists {Ω : Type*} (height : Ω → ℕ)
    (P : Ω → Prop) (hP : ∃ ω, P ω) :
    ∃ r : ℕ, ∃ ω, P ω ∧ height ω ≤ r := by
  obtain ⟨ω, hω⟩ := hP
  exact ⟨height ω, ω, hω, le_rfl⟩

private def witnessMinimumHeight {Ω : Type*} (height : Ω → ℕ)
    (P : Ω → Prop) (hP : ∃ ω, P ω) : ℕ :=
  Nat.find (witnessHeight_exists height P hP)

private def minimumHeightWitnessSet {Ω : Type*} (height : Ω → ℕ)
    (P : Ω → Prop) (hP : ∃ ω, P ω) : Set Ω :=
  {ω | P ω ∧ height ω ≤ witnessMinimumHeight height P hP}

private theorem minimumHeightWitnessSet_nonempty {Ω : Type*} (height : Ω → ℕ)
    (P : Ω → Prop) (hP : ∃ ω, P ω) :
    (minimumHeightWitnessSet height P hP).Nonempty :=
  Nat.find_spec (witnessHeight_exists height P hP)

private def minimumHeightWitness {Ω : Type*} (height : Ω → ℕ)
    (P : Ω → Prop) (hP : ∃ ω, P ω) : Ω :=
  (IsWellFounded.wf : WellFounded (@WellOrderingRel Ω)).min
    (minimumHeightWitnessSet height P hP)
    (minimumHeightWitnessSet_nonempty height P hP)

private theorem minimumHeightWitness_spec {Ω : Type*} (height : Ω → ℕ)
    (P : Ω → Prop) (hP : ∃ ω, P ω) :
    P (minimumHeightWitness height P hP) ∧
      height (minimumHeightWitness height P hP) = witnessMinimumHeight height P hP := by
  have h := (IsWellFounded.wf : WellFounded (@WellOrderingRel Ω)).min_mem
    (minimumHeightWitnessSet height P hP)
    (minimumHeightWitnessSet_nonempty height P hP)
  refine ⟨h.1, le_antisymm h.2 ?_⟩
  exact Nat.find_min' (witnessHeight_exists height P hP)
    ⟨minimumHeightWitness height P hP, h.1, le_rfl⟩

private theorem minimumHeightWitness_mutual {Ω : Type*} (height : Ω → ℕ)
    (P Q : Ω → Prop) (hP : ∃ ω, P ω) (hQ : ∃ ω, Q ω)
    (hPQ : P (minimumHeightWitness height Q hQ))
    (hQP : Q (minimumHeightWitness height P hP)) :
    minimumHeightWitness height Q hQ = minimumHeightWitness height P hP := by
  let ωP := minimumHeightWitness height P hP
  let ωQ := minimumHeightWitness height Q hQ
  have hsP := minimumHeightWitness_spec height P hP
  have hsQ := minimumHeightWitness_spec height Q hQ
  have hminPQ : witnessMinimumHeight height P hP ≤ witnessMinimumHeight height Q hQ := by
    apply Nat.find_min' (witnessHeight_exists height P hP)
    exact ⟨ωQ, hPQ, hsQ.2.le⟩
  have hminQP : witnessMinimumHeight height Q hQ ≤ witnessMinimumHeight height P hP := by
    apply Nat.find_min' (witnessHeight_exists height Q hQ)
    exact ⟨ωP, hQP, hsP.2.le⟩
  have hωQP : ωQ ∈ minimumHeightWitnessSet height P hP := by
    refine ⟨hPQ, ?_⟩
    rw [hsQ.2]
    exact hminQP
  have hωPQ : ωP ∈ minimumHeightWitnessSet height Q hQ := by
    refine ⟨hQP, ?_⟩
    rw [hsP.2]
    exact hminPQ
  have hnotQP : ¬ WellOrderingRel ωQ ωP :=
    (IsWellFounded.wf : WellFounded (@WellOrderingRel Ω)).not_lt_min
      (minimumHeightWitnessSet height P hP) (minimumHeightWitnessSet_nonempty height P hP) hωQP
  have hnotPQ : ¬ WellOrderingRel ωP ωQ :=
    (IsWellFounded.wf : WellFounded (@WellOrderingRel Ω)).not_lt_min
      (minimumHeightWitnessSet height Q hQ) (minimumHeightWitnessSet_nonempty height Q hQ) hωPQ
  rcases trichotomous_of (@WellOrderingRel Ω) ωQ ωP with h | h | h
  · exact False.elim (hnotQP h)
  · exact h
  · exact False.elim (hnotPQ h)

theorem exists_preferred_locally_constant_finiteWitness_selection {Ω : Type*}
    (height : Ω → ℕ) (P : Set ℕ → Ω → Prop)
    (hex : ∀ M : Set ℕ, M.Infinite → ∃ ω : Ω, P M ω) :
    ∃ φ : (M : Set ℕ) → M.Infinite → Ω,
      (∀ M hM, P M (φ M hM)) ∧
      (∀ M N hM hN, P M (φ N hN) → P N (φ M hM) → φ N hN = φ M hM) ∧
      (∀ M hM ω, P M ω → height (φ M hM) ≤ height ω) ∧
      ∀ M N hM hN,
        (∀ ω : Ω, height ω ≤ height (φ M hM) → (P M ω ↔ P N ω)) →
          φ N hN = φ M hM := by
  classical
  let φ : (M : Set ℕ) → M.Infinite → Ω := fun M hM =>
    minimumHeightWitness height (P M) (hex M hM)
  have hφ (M : Set ℕ) (hM : M.Infinite) : P M (φ M hM) ∧
      height (φ M hM) = witnessMinimumHeight height (P M) (hex M hM) :=
    minimumHeightWitness_spec height (P M) (hex M hM)
  refine ⟨φ, fun M hM => (hφ M hM).1, ?_, ?_, ?_⟩
  · intro M N hM hN hMN hNM
    exact minimumHeightWitness_mutual height (P M) (P N) (hex M hM) (hex N hN) hMN hNM
  · intro M hM ω hω
    rw [(hφ M hM).2]
    exact Nat.find_min' (witnessHeight_exists height (P M) (hex M hM)) ⟨ω, hω, le_rfl⟩
  intro M N hM hN hagree
  let rM := witnessMinimumHeight height (P M) (hex M hM)
  let rN := witnessMinimumHeight height (P N) (hex N hN)
  have hNM : rN ≤ rM := by
    apply Nat.find_min' (witnessHeight_exists height (P N) (hex N hN))
    refine ⟨φ M hM, ?_, (hφ M hM).2.le⟩
    exact (hagree _ le_rfl).mp (hφ M hM).1
  have hMN : rM ≤ rN := by
    apply Nat.find_min' (witnessHeight_exists height (P M) (hex M hM))
    refine ⟨φ N hN, ?_, (hφ N hN).2.le⟩
    apply (hagree _ ?_).mpr (hφ N hN).1
    rw [(hφ N hN).2, (hφ M hM).2]
    exact hNM
  have hr : rN = rM := le_antisymm hNM hMN
  have hsets : minimumHeightWitnessSet height (P N) (hex N hN) =
      minimumHeightWitnessSet height (P M) (hex M hM) := by
    ext ω
    change (P N ω ∧ height ω ≤ rN) ↔ (P M ω ∧ height ω ≤ rM)
    rw [hr]
    constructor
    · rintro ⟨hω, hheight⟩
      refine ⟨(hagree ω ?_).mpr hω, hheight⟩
      rwa [(hφ M hM).2]
    · rintro ⟨hω, hheight⟩
      refine ⟨(hagree ω ?_).mp hω, hheight⟩
      rwa [(hφ M hM).2]
  apply minimumHeightWitness_mutual height (P M) (P N) (hex M hM) (hex N hN)
  · apply (hagree _ ?_).mpr (hφ N hN).1
    rw [(hφ N hN).2, (hφ M hM).2]
    exact hNM
  · exact (hagree _ le_rfl).mp (hφ M hM).1

theorem exists_locally_constant_finiteWitness_selection {Ω : Type*}
    (height : Ω → ℕ) (P : Set ℕ → Ω → Prop)
    (hex : ∀ M : Set ℕ, M.Infinite → ∃ ω : Ω, P M ω) :
    ∃ φ : (M : Set ℕ) → M.Infinite → Ω,
      (∀ M hM, P M (φ M hM)) ∧
      ∀ M N hM hN,
        (∀ ω : Ω, height ω ≤ height (φ M hM) → (P M ω ↔ P N ω)) →
          φ N hN = φ M hM := by
  obtain ⟨φ, hvalid, _, _, hlocal⟩ :=
    exists_preferred_locally_constant_finiteWitness_selection height P hex
  exact ⟨φ, hvalid, hlocal⟩

end SurveyStatements.P1
