import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

/-- A bounded real-linear map commuting with multiplication by i is bounded
complex-linear. The real scalar structures need only satisfy the tower laws. -/
def complexLinearOfReal (f : E →L[ℝ] F)
    (hI : ∀ x, f (Complex.I • x) = Complex.I • f x) : E →L[ℂ] F where
  toFun := f
  map_add' := f.map_add
  map_smul' := by
    intro z x
    change f (z • x) = z • f x
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    calc
      f (z • x) = f (z.re • x + z.im • (Complex.I • x)) := by
        congr 1
        conv_lhs => rw [hz]
        rw [add_smul, smul_assoc, one_smul, smul_assoc]
      _ = z.re • f x + z.im • (Complex.I • f x) := by
        rw [f.map_add, f.map_smul, f.map_smul, hI]
      _ = z • f x := by
        conv_rhs => rw [hz]
        rw [add_smul, smul_assoc, one_smul, smul_assoc]
  cont := f.continuous

@[simp] theorem complexLinearOfReal_apply (f : E →L[ℝ] F) (hI) (x : E) :
    complexLinearOfReal f hI x = f x := rfl

end NonCalkinAlgebra
