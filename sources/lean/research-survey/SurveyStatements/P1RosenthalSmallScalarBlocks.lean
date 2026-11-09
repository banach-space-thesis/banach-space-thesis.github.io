import SurveyStatements.P1RosenthalCancellation

/-! Actual small blocks with nearly zero scalar sum, constructed from the
absence of a positive lower ℓ₁ estimate on every subsequence. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P1

theorem coefficientL1Mass_mapDomain (b : ℕ →₀ ℂ) (ν : ℕ → ℕ)
    (hν : Function.Injective ν) : coefficientL1Mass (b.mapDomain ν) = coefficientL1Mass b := by
  unfold coefficientL1Mass
  exact Finsupp.sum_mapDomain_index_inj hν

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem no_lower_l1_subsequence_exists_small_tail_block (s : ℕ → X)
    (hno : ∀ ν : ℕ → ℕ, StrictMono ν →
      ¬ ∃ L : ℝ, 0 < L ∧ ∀ b : ℕ →₀ ℂ,
        L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ (s ∘ ν) b‖)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ b : ℕ →₀ ℂ, (∀ i ∈ b.support, N ≤ i) ∧ coefficientL1Mass b = 1 ∧
      ‖Finsupp.linearCombination ℂ s b‖ ≤ ε := by
  classical
  let ν : ℕ → ℕ := fun n => n + N
  have hν : StrictMono ν := by intro i j hij; exact Nat.add_lt_add_right hij N
  obtain ⟨b, hb, hnorm⟩ :=
    no_lower_l1_estimate_exists_small_unit_mass_block (s ∘ ν) (hno ν hν) hε
  refine ⟨b.mapDomain ν, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hi)
    exact Nat.le_add_left N j
  · rw [coefficientL1Mass_mapDomain b ν hν.injective]
    exact hb
  · rw [Finsupp.linearCombination_mapDomain]
    exact hnorm.le

theorem small_tail_blocks_exists_disjoint_sequence (s : ℕ → X) {ε : ℝ}
    (hblocks : ∀ N : ℕ, ∃ b : ℕ →₀ ℂ,
      (∀ i ∈ b.support, N ≤ i) ∧ coefficientL1Mass b = 1 ∧
        ‖Finsupp.linearCombination ℂ s b‖ ≤ ε) :
    ∃ b : ℕ → ℕ →₀ ℂ,
      Pairwise (fun i j => Disjoint (b i).support (b j).support) ∧
      (∀ n, coefficientL1Mass (b n) = 1) ∧
      ∀ n, ‖Finsupp.linearCombination ℂ s (b n)‖ ≤ ε := by
  classical
  choose block hsupp hmass hnorm using hblocks
  let m : ℕ → ℕ := Nat.rec 0 (fun _ k => max (k + 1) ((block k).support.sup id + 1))
  let b : ℕ → ℕ →₀ ℂ := fun n => block (m n)
  have hmrec (n : ℕ) : m (n + 1) =
      max (m n + 1) ((b n).support.sup id + 1) := rfl
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hmrec]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hwindow (n i : ℕ) (hi : i ∈ (b n).support) : m n ≤ i ∧ i < m (n + 1) := by
    refine ⟨hsupp (m n) i hi, ?_⟩
    rw [hmrec]
    exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)).trans_le (le_max_right _ _)
  have hdislt {i j : ℕ} (hij : i < j) : Disjoint (b i).support (b j).support := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hklo : m j ≤ k := (hwindow j k hkj).1
    have hkhi : k < m (i + 1) := (hwindow i k hki).2
    have hpos : m (i + 1) ≤ m j := hm.monotone (Nat.succ_le_of_lt hij)
    exact (not_lt_of_ge (hpos.trans hklo)) hkhi
  refine ⟨b, ?_, fun n => hmass (m n), fun n => hnorm (m n)⟩
  intro i j hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hdislt h
  · exact (hdislt h).symm

theorem no_lower_l1_subsequence_exists_small_scalar_block (s : ℕ → X)
    (hno : ∀ ν : ℕ → ℕ, StrictMono ν →
      ¬ ∃ L : ℝ, 0 < L ∧ ∀ b : ℕ →₀ ℂ,
        L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ (s ∘ ν) b‖)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ b : ℕ →₀ ℂ, coefficientL1Mass b = 1 ∧
      ‖Finsupp.linearCombination ℂ s b‖ ≤ ε ∧ ‖coefficientScalarSum b‖ < τ := by
  obtain ⟨b, hdis, hmass, hnorm⟩ := small_tail_blocks_exists_disjoint_sequence s
    (no_lower_l1_subsequence_exists_small_tail_block s hno hε)
  exact disjoint_small_blocks_exists_small_scalar_sum s b hdis hmass hτ hnorm

end SurveyStatements.P1
