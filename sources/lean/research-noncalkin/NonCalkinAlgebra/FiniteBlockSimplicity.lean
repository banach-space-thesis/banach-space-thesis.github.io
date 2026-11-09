import NonCalkinAlgebra.FiniteBlockRefinement
import Mathlib.Data.Matrix.Basis

noncomputable section
set_option autoImplicit false

namespace NonCalkinAlgebra.FiniteBlockRefinement
open Matrix
universe u v

variable {D : Type u} {Q : D → Type u}
  [Fintype D] [∀ d, Fintype (Q d)] [∀ d, DecidableEq (Q d)]
variable {B : Type v} [Ring B] [Algebra ℂ B] [Nontrivial B]

/-- An element nonzero in every summand cannot be annihilated by a unital homomorphism. -/
theorem map_ne_zero_of_component_ne_zero (g : Blocks Q →ₐ[ℂ] B) (x : Blocks Q)
    (hx : ∀ d, x d ≠ 0) : g x ≠ 0 := by
  classical
  intro hgx
  have hdiag : ∀ (d : D) (i : Q d), g (Pi.single d (Matrix.single i i 1)) = 0 := by
    intro d i
    have hentry : ∃ a b : Q d, x d a b ≠ 0 := by
      by_contra! hn
      exact hx d (Matrix.ext hn)
    obtain ⟨a, b, hab⟩ := hentry
    let l : Blocks Q := Pi.single d (Matrix.single i a (x d a b)⁻¹)
    let r : Blocks Q := Pi.single d (Matrix.single b i 1)
    have hprod : l * x * r = Pi.single d (Matrix.single i i 1) := by
      funext e
      by_cases he : e = d
      · subst e
        simp only [l, r, Pi.mul_apply, Pi.single_eq_same, Matrix.single_mul_mul_single,
          inv_mul_cancel₀ hab, one_mul]
      · simp [l, r, Pi.single_eq_of_ne he]
    rw [← hprod, map_mul, map_mul, hgx, mul_zero, zero_mul]
  have hsum : (∑ d : D, ∑ i : Q d, Pi.single d (Matrix.single i i (1 : ℂ))) =
      (1 : Blocks Q) := by
    funext d
    change (∑ e : D, ∑ i : Q e, Pi.single e (Matrix.single i i (1 : ℂ))) d = _
    simp only [Finset.sum_apply]
    rw [Fintype.sum_eq_single d]
    · simp only [Pi.single_eq_same, Pi.one_apply]
      apply Matrix.ext
      intro a b
      simp only [Matrix.sum_apply, Matrix.single, Matrix.of_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst b
        simp
      · rw [if_neg hab]
        apply Finset.sum_eq_zero
        intro i _
        exact if_neg (fun h : i = a ∧ i = b => hab (h.1.symm.trans h.2))
    · intro e he
      simp [Pi.single_eq_of_ne (Ne.symm he)]
  have hz : g (1 : Blocks Q) = 0 := by
    rw [← hsum, map_sum]
    simp [map_sum, hdiag]
  exact one_ne_zero ((map_one g).symm.trans hz)

end NonCalkinAlgebra.FiniteBlockRefinement
