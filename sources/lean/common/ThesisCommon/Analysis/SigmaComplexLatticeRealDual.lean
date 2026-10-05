import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Complex.Basic

/-! The actual isometric real-linear identification of a complex Banach
space's complex dual with its full real dual. -/
noncomputable section
namespace ThesisCommon
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

def complexDualRealPart (φ : E →L[ℂ] ℂ) : E →L[ℝ] ℝ :=
  Complex.reCLM.comp (φ.restrictScalars ℝ)

@[simp] theorem complexDualRealPart_apply (φ : E →L[ℂ] ℂ) (x : E) :
    complexDualRealPart E φ x = (φ x).re := rfl

theorem extend_complexDualRealPart (φ : E →L[ℂ] ℂ) :
    (complexDualRealPart E φ).extendTo𝕜' = φ := by
  ext x
  change ((φ x).re : ℂ) - Complex.I * ((φ (Complex.I • x)).re : ℂ) = φ x
  rw [map_smul]
  apply Complex.ext <;> simp

theorem complexDualRealPart_extend (φ : E →L[ℝ] ℝ) :
    complexDualRealPart E (φ.extendTo𝕜' : E →L[ℂ] ℂ) = φ := by
  ext x
  exact LinearMap.extendTo𝕜'_apply_re (𝕜 := ℂ) φ.toLinearMap x

/-- Passing to real parts preserves the dual norm exactly and is onto the
full real dual; the inverse is `φ(x)-I φ(Ix)`. -/
def complexDualRealEquiv : (E →L[ℂ] ℂ) ≃ₗᵢ[ℝ] (E →L[ℝ] ℝ) where
  toFun := complexDualRealPart E
  invFun φ := φ.extendTo𝕜'
  left_inv := extend_complexDualRealPart E
  right_inv := complexDualRealPart_extend E
  map_add' φ ψ := by ext x; simp [complexDualRealPart]
  map_smul' r φ := by ext x; simp [complexDualRealPart]
  norm_map' φ := by
    have h := ContinuousLinearMap.norm_extendTo𝕜' (𝕜 := ℂ) (complexDualRealPart E φ)
    rw [extend_complexDualRealPart E] at h
    exact h.symm

@[simp] theorem complexDualRealEquiv_apply (φ : E →L[ℂ] ℂ) (x : E) :
    complexDualRealEquiv E φ x = (φ x).re := rfl

end ThesisCommon
