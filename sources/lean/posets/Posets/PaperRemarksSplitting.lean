import Posets.ProductIdealFiniteActive

/-! Remark 1.6: the actual continuous right inverse, and the algebra
identification obtained by padding one factor with zero factors. -/

noncomputable section
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem remark_1_6_continuous_right_inverse {E C : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C] [Mul C]
    (θ : BoundedHom 𝕜 (E →L[𝕜] E) C) (ρ : BoundedHom 𝕜 C (E →L[𝕜] E))
    (hs : StrongSplit 𝕜 E C θ ρ) :
    Continuous ρ ∧ (∀ a b, ρ (a * b) = ρ a * ρ b) ∧ ∀ a, θ (ρ a) = a :=
  ⟨ρ.toContinuousLinearMap.continuous, ρ.map_mul', hs.2.2⟩

/-- The paper numbers its first factor 1; the Lean sequence starts at 0. -/
def remark_1_6_single_factor_equiv (C : ℕ → Type)
    [∀ m, NormedRing (C m)] [∀ m, NormedAlgebra 𝕜 (C m)]
    (hz : ∀ m, 1 ≤ m → Subsingleton (C m)) : NormedProduct C ≃ₗᵢ[𝕜] C 0 :=
  { (normedProductPrefixLinearEquiv (𝕜 := 𝕜) C 1 hz).trans
      (LinearEquiv.piUnique 𝕜 (fun i : Fin 1 => C i.val)) with
    norm_map' := by
      intro x
      change ‖x 0‖ = ‖x‖
      apply le_antisymm (lp.norm_apply_le_norm ENNReal.top_ne_zero x 0)
      apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro m
      by_cases hm : m = 0
      · subst m
        exact le_rfl
      · letI := hz m (Nat.one_le_iff_ne_zero.mpr hm)
        rw [Subsingleton.elim (x m) 0, norm_zero]
        exact norm_nonneg _ }

theorem remark_1_6_single_factor_mul (C : ℕ → Type)
    [∀ m, NormedRing (C m)] [∀ m, NormedAlgebra 𝕜 (C m)]
    (hz : ∀ m, 1 ≤ m → Subsingleton (C m)) (x y : NormedProduct C) :
    remark_1_6_single_factor_equiv (𝕜 := 𝕜) C hz (x * y) =
      remark_1_6_single_factor_equiv (𝕜 := 𝕜) C hz x *
        remark_1_6_single_factor_equiv (𝕜 := 𝕜) C hz y := rfl

end Posets
