import NonCalkinAlgebra.TraceWeightRefinement
import Mathlib.Analysis.Complex.Norm

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TraceWeightRefinement
variable {R : Subring ℝ}

/-- The two coordinates of a trace, evaluated on minimal idempotents,
restrict across the block-diagonal maps by addition. -/
def CompatibleWeights (s : State R) (l r : ℕ → ℂ) : Prop :=
  ∀ n, if (s.stages n).rightWeight < (s.stages n).leftWeight then
    l n = l (n + 1) + r (n + 1) ∧ r n = r (n + 1)
  else
    l n = l (n + 1) ∧ r n = l (n + 1) + r (n + 1)

/-- A bounded sequence of trace differences with zero normalization
vanishes. The difference at any stage is a scalar times the vector of
opposite block sizes, whose sum grows without bound. -/
theorem compatible_difference_eq_zero (s : State R) (l r : ℕ → ℂ)
    (hcompat : CompatibleWeights s l r)
    (hnormal : (s.leftDim : ℂ) * l 0 + (s.rightDim : ℂ) * r 0 = 0)
    (C : ℝ) (hbounded : ∀ n, ‖l n‖ + ‖r n‖ ≤ C) :
    ∀ n, l n = 0 ∧ r n = 0 := by
  have hd : (s.rightDim : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.rightDim_pos)
  let z : ℂ := l 0 / (s.rightDim : ℂ)
  have hinit : l 0 = (s.rightDim : ℂ) * z := by
    dsimp [z]
    rw [mul_comm, div_mul_cancel₀ _ hd]
  have hrinit : r 0 = -(s.leftDim : ℂ) * z := by
    apply mul_left_cancel₀ hd
    calc
      (s.rightDim : ℂ) * r 0 = -((s.leftDim : ℂ) * l 0) := by
        calc
          _ = -((s.leftDim : ℂ) * l 0) +
              ((s.leftDim : ℂ) * l 0 + (s.rightDim : ℂ) * r 0) := by abel
          _ = _ := by rw [hnormal, add_zero]
      _ = (s.rightDim : ℂ) * (-(s.leftDim : ℂ) * z) := by rw [hinit]; ring
  have hform : ∀ n, l n = ((s.stages n).rightDim : ℂ) * z ∧
      r n = -((s.stages n).leftDim : ℂ) * z := by
    intro n
    induction n with
    | zero => exact ⟨hinit, hrinit⟩
    | succ n ih =>
      have hs := hcompat n
      by_cases hb : (s.stages n).rightWeight < (s.stages n).leftWeight
      · rw [if_pos hb] at hs
        rw [State.stages_succ, State.step, dif_pos hb]
        constructor
        · change l (n + 1) = (((s.stages n).leftDim + (s.stages n).rightDim : ℕ) : ℂ) * z
          calc
            l (n + 1) = l n - r n := by rw [hs.1, hs.2]; abel
            _ = _ := by rw [ih.1, ih.2, Nat.cast_add]; ring
        · exact hs.2.symm.trans ih.2
      · rw [if_neg hb] at hs
        rw [State.stages_succ, State.step, dif_neg hb]
        constructor
        · exact hs.1.symm.trans ih.1
        · change r (n + 1) = -((((s.stages n).leftDim + (s.stages n).rightDim : ℕ) : ℂ)) * z
          calc
            r (n + 1) = r n - l n := by rw [hs.2, hs.1]; abel
            _ = _ := by rw [ih.1, ih.2, Nat.cast_add]; ring
  have hz : z = 0 := by
    by_contra hne
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖z‖)
    have hlarge : C < (n : ℝ) * ‖z‖ := (div_lt_iff₀ hp).mp hn
    have hdims := s.dimension_sum_grows n
    have hnd : (n : ℝ) ≤ (((s.stages n).rightDim + (s.stages n).leftDim : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ (s.stages n).rightDim + (s.stages n).leftDim by omega)
    have hb := hbounded n
    rw [(hform n).1, (hform n).2, Complex.norm_mul, Complex.norm_mul, norm_neg,
      Complex.norm_natCast, Complex.norm_natCast, ← add_mul, ← Nat.cast_add] at hb
    exact (not_le_of_gt hlarge) ((mul_le_mul_of_nonneg_right hnd hp.le).trans hb)
  intro n
  simpa [hz] using hform n

end NonCalkinAlgebra.TraceWeightRefinement
