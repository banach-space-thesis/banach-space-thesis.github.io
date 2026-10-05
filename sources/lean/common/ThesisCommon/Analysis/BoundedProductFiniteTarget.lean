import ThesisCommon.Analysis.BoundedProductMasks
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite-dimensional targets admit arbitrarily small restrictions to
infinite coordinate bands in a genuine bounded product. The proof reduces
to finitely many scalar coordinates and thins the bands successively.
-/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem boundedProductMask_finite_target_small (S : lp E ∞ →L[𝕜] F)
    (J : Set ℕ) (hJ : J.Infinite) {η : ℝ} (hη : 0 < η) :
    ∃ I : Set ℕ, I ⊆ J ∧ I.Infinite ∧ ‖S.comp (boundedProductMask I)‖ < η := by
  classical
  let e := (Module.finBasis 𝕜 F).equivFunL
  let K : ℝ := max 1 ‖e.symm.toContinuousLinearMap‖
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  let δ := η / (2 * K)
  have hδ : 0 < δ := div_pos hη (mul_pos (by norm_num) hK)
  let f : Fin (Module.finrank 𝕜 F) → lp E ∞ →L[𝕜] 𝕜 := fun i =>
    ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap).comp S
  obtain ⟨I, hIJ, hI, hf⟩ := boundedProductMask_finite_scalar_small f Finset.univ J hJ hδ
  have hnorm : ‖S.comp (boundedProductMask I)‖ ≤ K * δ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK.le hδ.le)
    intro x
    have hcoord (i : Fin (Module.finrank 𝕜 F)) :
        ‖e (S (boundedProductMask (𝕜 := 𝕜) I x)) i‖ ≤ δ * ‖x‖ := by
      exact (((f i).comp (boundedProductMask I)).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hf i (Finset.mem_univ i)) (norm_nonneg x))
    have he : ‖e (S (boundedProductMask (𝕜 := 𝕜) I x))‖ ≤ δ * ‖x‖ :=
      (pi_norm_le_iff_of_nonneg (mul_nonneg hδ.le (norm_nonneg x))).mpr hcoord
    have hinv := e.symm.toContinuousLinearMap.le_opNorm
      (e (S (boundedProductMask (𝕜 := 𝕜) I x)))
    change ‖e.symm (e (S (boundedProductMask (𝕜 := 𝕜) I x)))‖ ≤
      ‖e.symm.toContinuousLinearMap‖ * ‖e (S (boundedProductMask (𝕜 := 𝕜) I x))‖ at hinv
    rw [e.symm_apply_apply] at hinv
    exact hinv.trans (by
      calc
        _ ≤ K * (δ * ‖x‖) := mul_le_mul (le_max_right _ _) he (norm_nonneg _) hK.le
        _ = (K * δ) * ‖x‖ := (mul_assoc _ _ _).symm)
  have hprod : K * δ = η / 2 := by
    dsimp only [δ]
    field_simp [ne_of_gt hK]
  exact ⟨I, hIJ, hI, hnorm.trans_lt (by rw [hprod]; exact half_lt_self hη)⟩

end ThesisCommon
