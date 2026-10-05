import PosetsCommon.CZeroSum

/-! For finite index sets the concrete c₀ sum is the full product with its
supremum norm. These identifications preserve the coordinate formulas. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [Fintype P]
  (X : P → Type) [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]

def finitePiToCZeroSum (x : ∀ p, X p) : DependentCZeroSum 𝕜 X :=
  ⟨⟨x, memℓp_infty ⟨‖x‖, by rintro _ ⟨p, rfl⟩; exact norm_le_pi_norm x p⟩⟩,
    by simp [cZeroSumSubmodule, cofinite_eq_bot]⟩

def finiteCZeroSumEquiv : DependentCZeroSum 𝕜 X ≃ₗᵢ[𝕜] (∀ p, X p) where
  toFun x p := x.val p
  invFun := finitePiToCZeroSum X
  left_inv x := by apply Subtype.ext; apply lp.ext; rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
        (fun p => lp.norm_apply_le_norm ENNReal.top_ne_zero x.val p)
    · exact lp.norm_le_of_forall_le (norm_nonneg (fun p => x.val p))
        (fun p => norm_le_pi_norm (fun q => x.val q) p)

theorem finiteCZeroSumEquiv_apply (x : DependentCZeroSum 𝕜 X) (p : P) :
    finiteCZeroSumEquiv X x p = x.val p := rfl

theorem finiteCZeroSumEquiv_symm_apply (x : ∀ p, X p) (p : P) :
    ((finiteCZeroSumEquiv (𝕜 := 𝕜) X).symm x).val p = x p := rfl

theorem finiteCZeroSumEquiv_injection (p : P) (x : X p) :
    finiteCZeroSumEquiv X (sumInjection 𝕜 X p x) = Pi.single p x := by
  classical
  rfl

end ThesisCommon
