import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra.TraceWeightRefinement

/-- Two positive, rationally independent weights for the minimal
idempotents of two matrix summands. Their dimension-weighted sum is one. -/
structure State (R : Subring ℝ) where
  leftDim : ℕ
  rightDim : ℕ
  leftWeight : ℝ
  rightWeight : ℝ
  leftDim_pos : 0 < leftDim
  rightDim_pos : 0 < rightDim
  leftWeight_pos : 0 < leftWeight
  rightWeight_pos : 0 < rightWeight
  leftWeight_mem : leftWeight ∈ R
  rightWeight_mem : rightWeight ∈ R
  independent : ∀ m n : ℤ, (m : ℝ) * leftWeight + (n : ℝ) * rightWeight = 0 →
    m = 0 ∧ n = 0
  normalized : (leftDim : ℝ) * leftWeight + (rightDim : ℝ) * rightWeight = 1

namespace State
variable {R : Subring ℝ}

def initial (θ : ℝ) (h₀ : 0 < θ) (h₁ : θ < 1) (hm : θ ∈ R)
    (hirr : ∀ q : ℚ, (q : ℝ) ≠ θ) : State R where
  leftDim := 1
  rightDim := 1
  leftWeight := θ
  rightWeight := 1 - θ
  leftDim_pos := Nat.zero_lt_one
  rightDim_pos := Nat.zero_lt_one
  leftWeight_pos := h₀
  rightWeight_pos := sub_pos.mpr h₁
  leftWeight_mem := hm
  rightWeight_mem := R.sub_mem R.one_mem hm
  independent := by
    intro m n h
    have hmn : m = n := by
      by_contra hne
      have hden : (m : ℝ) - (n : ℝ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast hne)
      apply hirr (-(n : ℚ) / ((m : ℚ) - (n : ℚ)))
      push_cast
      apply (div_eq_iff hden).2
      linarith only [h]
    subst m
    have hn : (n : ℝ) = 0 := by linarith only [h]
    have hn' : n = 0 := by exact_mod_cast hn
    exact ⟨hn', hn'⟩
  normalized := by simp

theorem weights_ne (s : State R) : s.leftWeight ≠ s.rightWeight := by
  intro h
  have hbad := (s.independent 1 (-1) (by push_cast; linarith)).1
  omega

/-- Split each tile of the longer left kind into one tile of each new kind.
The old right tiles retain their length. -/
def subtractLeft (s : State R) (h : s.rightWeight < s.leftWeight) : State R where
  leftDim := s.leftDim
  rightDim := s.leftDim + s.rightDim
  leftWeight := s.leftWeight - s.rightWeight
  rightWeight := s.rightWeight
  leftDim_pos := s.leftDim_pos
  rightDim_pos := by have := s.rightDim_pos; omega
  leftWeight_pos := sub_pos.mpr h
  rightWeight_pos := s.rightWeight_pos
  leftWeight_mem := R.sub_mem s.leftWeight_mem s.rightWeight_mem
  rightWeight_mem := s.rightWeight_mem
  independent := by
    intro m n hz
    have hc : (m : ℝ) * s.leftWeight + ((n - m : ℤ) : ℝ) * s.rightWeight = 0 := by
      push_cast
      linarith only [hz]
    obtain ⟨hm, hnm⟩ := s.independent m (n - m) hc
    exact ⟨hm, by omega⟩
  normalized := by
    calc
      (s.leftDim : ℝ) * (s.leftWeight - s.rightWeight) +
          ((s.leftDim + s.rightDim : ℕ) : ℝ) * s.rightWeight =
          (s.leftDim : ℝ) * s.leftWeight + (s.rightDim : ℝ) * s.rightWeight := by
            push_cast
            ring
      _ = 1 := s.normalized

/-- The other refinement, with all right tiles split and left lengths retained. -/
def subtractRight (s : State R) (h : s.leftWeight < s.rightWeight) : State R where
  leftDim := s.leftDim + s.rightDim
  rightDim := s.rightDim
  leftWeight := s.leftWeight
  rightWeight := s.rightWeight - s.leftWeight
  leftDim_pos := by have := s.leftDim_pos; omega
  rightDim_pos := s.rightDim_pos
  leftWeight_pos := s.leftWeight_pos
  rightWeight_pos := sub_pos.mpr h
  leftWeight_mem := s.leftWeight_mem
  rightWeight_mem := R.sub_mem s.rightWeight_mem s.leftWeight_mem
  independent := by
    intro m n hz
    have hc : ((m - n : ℤ) : ℝ) * s.leftWeight + (n : ℝ) * s.rightWeight = 0 := by
      push_cast
      linarith only [hz]
    obtain ⟨hmn, hn⟩ := s.independent (m - n) n hc
    exact ⟨by omega, hn⟩
  normalized := by
    calc
      ((s.leftDim + s.rightDim : ℕ) : ℝ) * s.leftWeight +
          (s.rightDim : ℝ) * (s.rightWeight - s.leftWeight) =
          (s.leftDim : ℝ) * s.leftWeight + (s.rightDim : ℝ) * s.rightWeight := by
            push_cast
            ring
      _ = 1 := s.normalized

def step (s : State R) : State R :=
  if h : s.rightWeight < s.leftWeight then s.subtractLeft h
  else s.subtractRight (lt_of_le_of_ne (le_of_not_gt h) s.weights_ne)

def stages (s : State R) : ℕ → State R
  | 0 => s
  | n + 1 => (stages s n).step

@[simp] theorem stages_zero (s : State R) : s.stages 0 = s := rfl
@[simp] theorem stages_succ (s : State R) (n : ℕ) :
    s.stages (n + 1) = (s.stages n).step := rfl

theorem dimension_sum_lt_step (s : State R) :
    s.leftDim + s.rightDim < s.step.leftDim + s.step.rightDim := by
  unfold step
  split
  · change s.leftDim + s.rightDim < s.leftDim + (s.leftDim + s.rightDim)
    have := s.leftDim_pos
    omega
  · change s.leftDim + s.rightDim < s.leftDim + s.rightDim + s.rightDim
    have := s.rightDim_pos
    omega

theorem dimension_sum_grows (s : State R) (n : ℕ) :
    s.leftDim + s.rightDim + n ≤ (s.stages n).leftDim + (s.stages n).rightDim := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (s.stages n).dimension_sum_lt_step
    rw [stages_succ]
    omega

end State
end NonCalkinAlgebra.TraceWeightRefinement
