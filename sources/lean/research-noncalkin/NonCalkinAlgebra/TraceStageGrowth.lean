import NonCalkinAlgebra.TraceWeightRefinement

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TraceWeightRefinement.State
variable {R : Subring ℝ}

/-- From every level one eventually splits the left summand. If this
never happens, the left weight is fixed while its dimension grows. -/
theorem exists_later_left (s : State R) (n : ℕ) :
    ∃ k ≥ n, (s.stages k).rightWeight < (s.stages k).leftWeight := by
  by_contra! hall
  have hg : ∀ k : ℕ, (s.stages (n + k)).leftWeight = (s.stages n).leftWeight ∧
      k ≤ (s.stages (n + k)).leftDim := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hb := not_lt_of_ge (hall (n + k) (by omega))
      have hp := (s.stages (n + k)).rightDim_pos
      rw [Nat.add_succ, stages_succ, step, dif_neg hb]
      exact ⟨ih.1, by
        change k + 1 ≤ (s.stages (n + k)).leftDim + (s.stages (n + k)).rightDim
        omega⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (s.stages n).leftWeight)
  have hk' := (div_lt_iff₀ (s.stages n).leftWeight_pos).mp hk
  have hd : (k : ℝ) ≤ ((s.stages (n + k)).leftDim : ℝ) := by exact_mod_cast (hg k).2
  have ht := hk'.trans_le (mul_le_mul_of_nonneg_right hd (s.stages n).leftWeight_pos.le)
  rw [← (hg k).1] at ht
  have hr : 0 < ((s.stages (n + k)).rightDim : ℝ) * (s.stages (n + k)).rightWeight :=
    mul_pos (Nat.cast_pos.mpr (s.stages (n + k)).rightDim_pos)
      (s.stages (n + k)).rightWeight_pos
  linarith [(s.stages (n + k)).normalized]

/-- From every level one eventually splits the right summand as well. -/
theorem exists_later_right (s : State R) (n : ℕ) :
    ∃ k ≥ n, (s.stages k).leftWeight < (s.stages k).rightWeight := by
  by_contra! hall
  have hg : ∀ k : ℕ, (s.stages (n + k)).rightWeight = (s.stages n).rightWeight ∧
      k ≤ (s.stages (n + k)).rightDim := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hb : (s.stages (n + k)).rightWeight < (s.stages (n + k)).leftWeight :=
        lt_of_le_of_ne (hall (n + k) (by omega)) (s.stages (n + k)).weights_ne.symm
      have hp := (s.stages (n + k)).leftDim_pos
      rw [Nat.add_succ, stages_succ, step, dif_pos hb]
      exact ⟨ih.1, by
        change k + 1 ≤ (s.stages (n + k)).leftDim + (s.stages (n + k)).rightDim
        omega⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (s.stages n).rightWeight)
  have hk' := (div_lt_iff₀ (s.stages n).rightWeight_pos).mp hk
  have hd : (k : ℝ) ≤ ((s.stages (n + k)).rightDim : ℝ) := by exact_mod_cast (hg k).2
  have ht := hk'.trans_le (mul_le_mul_of_nonneg_right hd (s.stages n).rightWeight_pos.le)
  rw [← (hg k).1] at ht
  have hl : 0 < ((s.stages (n + k)).leftDim : ℝ) * (s.stages (n + k)).leftWeight :=
    mul_pos (Nat.cast_pos.mpr (s.stages (n + k)).leftDim_pos)
      (s.stages (n + k)).leftWeight_pos
  linarith [(s.stages (n + k)).normalized]

end NonCalkinAlgebra.TraceWeightRefinement.State
