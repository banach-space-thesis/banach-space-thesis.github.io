import NonCalkinAlgebra.BlockTraceCompatibility

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
open Matrix
universe u

variable {C D : Type u} {P : C → Type u} {Q : D → Type u}
variable [Fintype C] [Fintype D]
variable [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
variable [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]

open Classical in
def rankOne (P : C → Type u) [∀ c, DecidableEq (P c)] (c : C) (i : P c) : Blocks P :=
  Pi.single c (Matrix.single i i 1)

open Classical in
theorem rankOne_trace (c : C) (i : P c) (d : C) :
    (rankOne P c i d).trace = if d = c then (1 : ℂ) else 0 := by
  classical
  by_cases h : d = c
  · subst d
    simp [rankOne]
  · simp [rankOne, h]

theorem rankOne_sq (c : C) (i : P c) : rankOne P c i * rankOne P c i = rankOne P c i := by
  classical
  funext d
  by_cases h : d = c
  · subst d
    simp [rankOne]
  · simp [rankOne, h]

theorem rankOne_star (c : C) (i : P c) : star (rankOne P c i) = rankOne P c i := by
  classical
  funext d
  by_cases h : d = c
  · subst d
    simp [rankOne, Matrix.star_eq_conjTranspose]
  · simp [rankOne, h]

/-- The coefficients of an arbitrary finite-stage trace are its values on matrix units. -/
theorem linearTrace_eq_sum (L : Blocks P →ₗ[ℂ] ℂ)
    (hL : ∀ x y, L (x * y) = L (y * x)) (row : ∀ c, P c) (x : Blocks P) :
    L x = ∑ c, L (rankOne P c (row c)) * (x c).trace := by
  classical
  have hsum : (∑ c : C, Pi.single c (x c)) = x := by
    funext d
    simp only [Finset.sum_apply]
    rw [Fintype.sum_eq_single d]
    · simp
    · intro c hc
      simp [Pi.single_eq_of_ne hc.symm]
  calc
    L x = ∑ c : C, L (Pi.single c (x c)) := by
      simpa only [map_sum] using (congrArg L hsum).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      let Lc := L.comp (LinearMap.single ℂ (fun d => Matrix (P d) (P d) ℂ) c)
      have hsingle (a b : Matrix (P c) (P c) ℂ) :
          Pi.single c (a * b) = (Pi.single c a : Blocks P) * Pi.single c b := by
        funext d
        by_cases hd : d = c
        · subst d
          simp
        · simp [Pi.single_eq_of_ne hd]
      have hLc (a b : Matrix (P c) (P c) ℂ) : Lc (a * b) = Lc (b * a) := by
        change L (Pi.single c (a * b)) = L (Pi.single c (b * a))
        rw [hsingle, hsingle]
        exact hL _ _
      exact TraceFiniteMatrices.linear_trace_eq Lc hLc (row c) (x c)

open Classical in
theorem traceCoefficients_compatible (f : Refinement P Q) [∀ d, Fintype (f.Copies d)]
    (L : Blocks P →ₗ[ℂ] ℂ) (M : Blocks Q →ₗ[ℂ] ℂ)
    (hM : ∀ x y, M (x * y) = M (y * x))
    (h : ∀ x, M (f.hom x) = L x)
    (c : C) (i : P c) (row : ∀ d, Q d) :
    L (rankOne P c i) = ∑ d, ∑ k : f.Copies d,
      if f.color d k = c then M (rankOne Q d (row d)) else 0 := by
  classical
  rw [← h, linearTrace_eq_sum M hM row]
  simp only [f.trace_hom, Finset.mul_sum, rankOne_trace, mul_ite, mul_one, mul_zero]

end NonCalkinAlgebra.FiniteBlockRefinement
