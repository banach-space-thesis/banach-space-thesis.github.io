import SurveyStatements.P1C0OffBlock

/-! Finite synthesis of disjoint coefficient-unit c₀ blocks. -/

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace SurveyStatements.P1

theorem finsuppBlockSynthesis_support (b : ℕ → ℕ →₀ ℂ) (a : ℕ →₀ ℂ)
    {i : ℕ} (hi : i ∈ (Finsupp.linearCombination ℂ b a).support) :
    ∃ j ∈ a.support, i ∈ (b j).support := by
  classical
  by_contra h
  push_neg at h
  have hzero : Finsupp.linearCombination ℂ b a i = 0 := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply,
      Finsupp.smul_apply]
    exact Finset.sum_eq_zero fun j hj => by simp [Finsupp.notMem_support_iff.mp (h j hj)]
  exact Finsupp.mem_support_iff.mp hi hzero

theorem finsuppBlockSynthesis_coeff_bound (b : ℕ → ℕ →₀ ℂ)
    (hdisjoint : ∀ n k, n ≠ k → Disjoint (b n).support (b k).support)
    (hb : ∀ n i, ‖b n i‖ ≤ 1) (a : ℕ →₀ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) :
    ∀ i, ‖Finsupp.linearCombination ℂ b a i‖ ≤ C := by
  classical
  intro i
  by_cases hz : Finsupp.linearCombination ℂ b a i = 0
  · simpa [hz] using hC
  · obtain ⟨j, hj, hij⟩ := finsuppBlockSynthesis_support b a (Finsupp.mem_support_iff.mpr hz)
    have hEq : Finsupp.linearCombination ℂ b a i = a j * b j i := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply,
        Finsupp.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_single j
      · intro k hk hkj
        have hik : i ∉ (b k).support := fun hik =>
          Finset.disjoint_left.mp (hdisjoint j k hkj.symm) hij hik
        simp [Finsupp.notMem_support_iff.mp hik]
      · exact fun hnot => False.elim (hnot hj)
    rw [hEq, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb j i) (norm_nonneg _)).trans
      (by simpa using ha j)

theorem finsuppBlockSynthesis_tail_support (b : ℕ → ℕ →₀ ℂ) (N : ℕ)
    (hsupp : ∀ j i, i ∈ (b j).support → N ≤ i) (a : ℕ →₀ ℂ) :
    ∀ i ∈ (Finsupp.linearCombination ℂ b a).support, N ≤ i := by
  intro i hi
  obtain ⟨j, _, hij⟩ := finsuppBlockSynthesis_support b a hi
  exact hsupp j i hij

theorem finsuppBlockSynthesis_erase_disjoint (b : ℕ → ℕ →₀ ℂ)
    (hdisjoint : ∀ n k, n ≠ k → Disjoint (b n).support (b k).support)
    (a : ℕ →₀ ℂ) (j : ℕ) :
    Disjoint (b j).support (Finsupp.linearCombination ℂ b (a.erase j)).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hij hi
  obtain ⟨k, hk, hik⟩ := finsuppBlockSynthesis_support b (a.erase j) hi
  have hkj : k ≠ j := by
    intro h
    subst k
    simpa using hk
  exact Finset.disjoint_left.mp (hdisjoint j k hkj.symm) hij hik

end SurveyStatements.P1
