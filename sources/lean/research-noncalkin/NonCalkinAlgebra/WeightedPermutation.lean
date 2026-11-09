import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
open scoped ENNReal
universe u

/-- The actual complex Hilbert-space norm, without any finite-support restriction. -/
abbrev SquareSummable (I : Type u) := lp (fun _ : I => ℂ) 2

variable {I : Type u}

theorem weightedPermutation_mem (σ : I ≃ I) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (f : SquareSummable I) :
    Memℓp (fun i => z i * f (σ i)) 2 := by
  have hf : Summable (fun i : I => ‖f i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp f).summable (by norm_num)
  apply memℓp_gen
  simpa only [norm_mul, hz, one_mul] using σ.summable_iff.mpr hf

/-- A permutation of coordinates, weighted by arbitrary complex numbers of
modulus one, is a complex linear isometry on the full l2 space. -/
def weightedPermutation (σ : I ≃ I) (z : I → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    SquareSummable I →ₗᵢ[ℂ] SquareSummable I where
  toFun f := ⟨fun i => z i * f (σ i), weightedPermutation_mem σ z hz f⟩
  map_add' f g := by
    apply lp.ext
    funext i
    exact mul_add _ _ _
  map_smul' c f := by
    apply lp.ext
    funext i
    change z i * (c * f (σ i)) = c * (z i * f (σ i))
    ring
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' i, ‖z i * f (σ i)‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal
    simp_rw [norm_mul, hz, one_mul]
    exact σ.tsum_eq (fun i : I => ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem weightedPermutation_apply (σ : I ≃ I) (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (f : SquareSummable I) (i : I) :
    weightedPermutation σ z hz f i = z i * f (σ i) := rfl

end NonCalkinAlgebra
