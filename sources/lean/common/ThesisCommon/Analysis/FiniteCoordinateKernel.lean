import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! Finite scalar coordinate families cannot separate an infinite-
dimensional subspace. The resulting common kernel contains a unit vector;
the subspace need not be closed. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem exists_unit_in_subspace_annihilating_finite_family
    (E : Submodule 𝕜 X) (hE : ¬ FiniteDimensional 𝕜 E) {N : ℕ}
    (φ : Fin N → X →L[𝕜] 𝕜) :
    ∃ x : X, x ∈ E ∧ ‖x‖ = 1 ∧ ∀ i, φ i x = 0 := by
  classical
  let f : E →ₗ[𝕜] (Fin N → 𝕜) := {
    toFun := fun x i => φ i x.val
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro c x; ext i; simp
  }
  have hninj : ¬ Function.Injective f := fun h => hE (FiniteDimensional.of_injective f h)
  rw [Function.Injective] at hninj
  push_neg at hninj
  obtain ⟨x, y, hxy, hne⟩ := hninj
  have hn : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let z : E := ((‖x-y‖⁻¹ : ℝ) : 𝕜) • (x-y)
  refine ⟨z.val, z.property, ?_, ?_⟩
  · change ‖z‖ = 1
    dsimp only [z]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · intro i
    have hh : f (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    have hi := congrFun hh i
    change φ i ((x-y : E).val) = 0 at hi
    change φ i (((‖x-y‖⁻¹ : ℝ) : 𝕜) • (x-y : E).val) = 0
    rw [map_smul, hi, smul_zero]

end ThesisCommon
