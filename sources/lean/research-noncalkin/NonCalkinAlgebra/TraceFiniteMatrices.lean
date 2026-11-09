import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Matrix.Basis

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.TraceFiniteMatrices
open Matrix
open scoped BigOperators

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

/-- An idempotent matrix has trace equal to the dimension of its range. -/
theorem trace_idempotent (x : Matrix I I ℂ) (hx : x * x = x) :
    ∃ n : ℕ, x.trace = n := by
  have h : IsIdempotentElem x.toLin' := by
    change x.toLin' * x.toLin' = x.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hx]
  have hp := (LinearMap.isProj_range_iff_isIdempotentElem x.toLin').2 h
  exact ⟨Module.finrank ℂ (LinearMap.range x.toLin'),
    x.trace_toLin'_eq.symm.trans hp.trace⟩

/-- The scalar multiple is determined by the value on any rank-one diagonal matrix unit. -/
theorem linear_trace_eq (L : Matrix I I ℂ →ₗ[ℂ] ℂ)
    (hL : ∀ x y, L (x * y) = L (y * x)) (i₀ : I) (x : Matrix I I ℂ) :
    L x = L (Matrix.single i₀ i₀ 1) * x.trace := by
  have hdiag (i : I) : L (Matrix.single i i 1) = L (Matrix.single i₀ i₀ 1) := by
    simpa only [Matrix.single_mul_single_same, mul_one] using
      hL (Matrix.single i i₀ 1) (Matrix.single i₀ i 1)
  have hoff (i j : I) (hij : i ≠ j) : L (Matrix.single i j 1) = 0 := by
    have hzero : Matrix.single i j (1 : ℂ) * Matrix.single i i 1 = 0 := by
      exact Matrix.single_mul_single_of_ne 1 i j i hij.symm 1
    simpa only [Matrix.single_mul_single_same, hzero, mul_one, map_zero] using
      hL (Matrix.single i i 1) (Matrix.single i j 1)
  have hentry (i j : I) :
      L (Matrix.single i j (x i j)) =
        if i = j then L (Matrix.single i₀ i₀ 1) * x i i else 0 := by
    have hscale : (x i j) • Matrix.single i j (1 : ℂ) = Matrix.single i j (x i j) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [← hscale]
    rw [map_smul, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      rw [hdiag, if_pos rfl, mul_comm]
    · rw [hoff _ _ hij, if_neg hij, mul_zero]
  calc
    L x = ∑ i : I, ∑ j : I, L (Matrix.single i j (x i j)) := by
      simpa only [map_sum] using congrArg L (Matrix.matrix_eq_sum_single x)
    _ = ∑ i : I, L (Matrix.single i₀ i₀ 1) * x i i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hentry]
      exact Fintype.sum_ite_eq i (fun _ => L (Matrix.single i₀ i₀ 1) * x i i)
    _ = _ := by rw [Matrix.trace, Finset.mul_sum]; rfl

end NonCalkinAlgebra.TraceFiniteMatrices
