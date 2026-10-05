import PosetsCommon.CZeroSum

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜] {P Z : Type*}
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {X : P → Type*} [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace 𝕜 (X p)]

def finiteLift (F : Finset P) (c : P → 𝕜) (j : ∀ p, Z →L[𝕜] X p) :
    Z →L[𝕜] DependentCZeroSum 𝕜 X :=
  ∑ p ∈ F, c p • (sumInjection 𝕜 X p).comp (j p)

theorem finiteLift_apply (F : Finset P) (c : P → 𝕜) (j : ∀ p, Z →L[𝕜] X p)
    (z : Z) (q : P) :
    (finiteLift F c j z).val q = if q ∈ F then c q • j q z else 0 := by
  simp [finiteLift, sumInjection]
  by_cases hq : q ∈ F
  · rw [if_pos hq, Finset.sum_eq_single q]
    · simp
    · intro p _ hpq
      simp [Pi.single_eq_of_ne hpq.symm]
    · exact fun hnot => False.elim (hnot hq)
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro p hp
    have hqp : q ≠ p := fun heq => hq (heq.symm ▸ hp)
    simp [Pi.single_eq_of_ne hqp]

theorem finiteLift_bound (F : Finset P) (c : P → 𝕜) (j : ∀ p, Z →ₗᵢ[𝕜] X p)
    (hc : ∀ p ∈ F, ‖c p‖ ≤ 1) (z : Z) :
    ‖finiteLift F c (fun p => (j p).toContinuousLinearMap) z‖ ≤ ‖z‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg z)
  intro q
  change ‖(finiteLift F c (fun p => (j p).toContinuousLinearMap) z).val q‖ ≤ ‖z‖
  rw [finiteLift_apply]
  split_ifs with hq
  · simpa only [norm_smul, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
      one_mul] using mul_le_mul_of_nonneg_right (hc q hq) (norm_nonneg z)
  · simp only [norm_zero]
    exact norm_nonneg z

theorem sumProjection_norm_le (x : DependentCZeroSum 𝕜 X) (p : P) :
    ‖sumProjection 𝕜 X p x‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.val p

end ThesisCommon
