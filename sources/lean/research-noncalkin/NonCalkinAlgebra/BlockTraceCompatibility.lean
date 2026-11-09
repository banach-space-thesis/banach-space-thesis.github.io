import NonCalkinAlgebra.WeightedBlockTrace
import NonCalkinAlgebra.FiniteBlockComposition

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement.Refinement
open NonCalkinAlgebra.FiniteBlockRefinement

universe u
variable {C D : Type u} {P : C → Type u} {Q : D → Type u}
variable [Fintype C] [Fintype D]
variable (f : Refinement P Q) [∀ d, Fintype (f.Copies d)]

open Classical in
/-- The trace weight of a rank-one source projection is the sum
of the weights of its copies in the target blocks. -/
def WeightLaw (w : C → ℝ) (v : D → ℝ) : Prop :=
  ∀ c, (∑ d, ∑ k : f.Copies d, if f.color d k = c then v d else 0) = w c

theorem weightedBlockTrace_map
    [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
    (w : C → ℝ) (v : D → ℝ) (h : f.WeightLaw w v) (x : Blocks P) :
    weightedBlockTrace v (f.hom x) = weightedBlockTrace w x := by
  classical
  have hlaw (c : C) :
      (∑ d, ∑ k : f.Copies d, if f.color d k = c then (v d : ℂ) else 0) = (w c : ℂ) := by
    have hc := congrArg Complex.ofReal (h c)
    push_cast at hc
    simpa only [apply_ite, Complex.ofReal_zero] using hc
  change (∑ d, (v d : ℂ) * (f.hom x d).trace) = ∑ c, (w c : ℂ) * (x c).trace
  calc
    _ = ∑ d, ∑ k : f.Copies d, (v d : ℂ) * (x (f.color d k)).trace := by
      simp only [trace_hom, Finset.mul_sum]
    _ = ∑ d, ∑ k : f.Copies d, ∑ c : C,
        (if f.color d k = c then (v d : ℂ) else 0) * (x c).trace := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_eq_single (f.color d k)]
      · rw [if_pos rfl]
      · intro c hc
        rw [if_neg hc.symm, zero_mul]
    _ = ∑ d, ∑ c : C, ∑ k : f.Copies d,
        (if f.color d k = c then (v d : ℂ) else 0) * (x c).trace := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ c : C, ∑ d, ∑ k : f.Copies d,
        (if f.color d k = c then (v d : ℂ) else 0) * (x c).trace :=
      Finset.sum_comm
    _ = ∑ c : C, (∑ d, ∑ k : f.Copies d,
        if f.color d k = c then (v d : ℂ) else 0) * (x c).trace := by
      simp only [Finset.sum_mul]
    _ = _ := by simp only [hlaw]


theorem weightLaw_of_weightedBlockTrace_map
    [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)] [∀ c, Nonempty (P c)]
    [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
    (w : C → ℝ) (v : D → ℝ)
    (h : ∀ x, weightedBlockTrace v (f.hom x) = weightedBlockTrace w x) :
    f.WeightLaw w v := by
  classical
  intro c
  let i : P c := Classical.choice inferInstance
  let p : Blocks P := Pi.single c (Matrix.single i i 1)
  have htrace (d : C) : (p d).trace = if d = c then (1 : ℂ) else 0 := by
    by_cases hd : d = c
    · subst d
      simp [p]
    · simp [p, Pi.single_eq_of_ne hd, hd]
  have hc := h p
  change (∑ d, (v d : ℂ) * (f.hom p d).trace) =
    ∑ d, (w d : ℂ) * (p d).trace at hc
  simp only [trace_hom, htrace, Finset.mul_sum, mul_ite, mul_zero, mul_one, Fintype.sum_ite_eq'] at hc
  apply Complex.ofReal_injective
  push_cast
  simpa only [apply_ite, Complex.ofReal_zero] using hc

end NonCalkinAlgebra.FiniteBlockRefinement.Refinement
