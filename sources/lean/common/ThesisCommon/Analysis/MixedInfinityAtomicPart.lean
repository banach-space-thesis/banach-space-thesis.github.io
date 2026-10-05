import ThesisCommon.Analysis.MixedInfinityEstimates

/-! The actual absolutely convergent matrix functional on X(ell_infinity).
Finite coordinate phase changes are contractive in the genuine sum norm. -/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

theorem infinity_finite_sum_apply (F : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → 𝕜) (i j : ℕ) :
    (∑ p ∈ F, a p • single (b := b) (hb := hb) (Y := lp (fun _ : ℕ => 𝕜) ∞) p.1
      (lp.single ∞ p.2 (1 : 𝕜))) i j = if (i, j) ∈ F then a (i, j) else 0 := by
  classical
  rw [sum_apply]
  simp only [smul_apply, single_apply, lp.coeFn_sum, Finset.sum_apply]
  have hterm (p : ℕ × ℕ) : (a p • (if i = p.1 then lp.single ∞ p.2 (1 : 𝕜)
      else (0 : lp (fun _ : ℕ => 𝕜) ∞))) j = if p = (i, j) then a p else 0 := by
    by_cases hi : i = p.1
    · by_cases hj : j = p.2
      · have hp : p = (i, j) := Prod.ext hi.symm hj.symm
        simp only [if_pos hi, if_pos hp, lp.coeFn_smul, Pi.smul_apply,
          lp.single_apply, Pi.single_apply, if_pos hj, smul_eq_mul, mul_one]
      · have hp : p ≠ (i, j) := fun h => hj (congrArg Prod.snd h).symm
        simp only [if_pos hi, if_neg hp, lp.coeFn_smul, Pi.smul_apply,
          lp.single_apply, Pi.single_apply, if_neg hj, smul_eq_mul, mul_zero]
    · have hp : p ≠ (i, j) := fun h => hi (congrArg Prod.fst h).symm
      simp only [if_neg hi, if_neg hp, smul_zero, lp.coeFn_zero, Pi.zero_apply]
  simp_rw [hterm]
  exact Finset.sum_ite_eq' F (i, j) a

theorem infinity_finite_sum_norm_le
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞))
    (F : Finset (ℕ × ℕ)) (a : (ℕ × ℕ) → 𝕜)
    (ha : ∀ p ∈ F, ‖a p‖ ≤ ‖x p.1 p.2‖) :
    ‖∑ p ∈ F, a p • single (b := b) (hb := hb) (Y := lp (fun _ : ℕ => 𝕜) ∞) p.1
      (lp.single ∞ p.2 (1 : 𝕜))‖ ≤ ‖x‖ := by
  classical
  apply norm_le_of_apply_le _ x
  intro i
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro j
  rw [infinity_finite_sum_apply]
  split_ifs with hp
  · exact (ha (i, j) hp).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero _ j)
  · simp only [norm_zero]; exact norm_nonneg _

theorem infinity_weighted_finite_sum_le
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (F : Finset (ℕ × ℕ)) :
    ∑ p ∈ F, ‖x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜)))‖ ≤ ‖φ‖ * ‖x‖ := by
  classical
  choose a ha hphase using fun p : ℕ × ℕ => RCLike.exists_norm_eq_mul_self
    (x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜))))
  let y := ∑ p ∈ F, (a p * x p.1 p.2) • single (b := b) (hb := hb)
    (Y := lp (fun _ : ℕ => 𝕜) ∞) p.1
    (lp.single ∞ p.2 (1 : 𝕜))
  have hy : ‖y‖ ≤ ‖x‖ := infinity_finite_sum_norm_le x F _ (fun p _ => by
    rw [norm_mul, ha, one_mul])
  have heq : φ y = ((∑ p ∈ F,
      ‖x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜)))‖ : ℝ) : 𝕜) := by
    dsimp [y]
    rw [RCLike.ofReal_sum]
    simp only [map_sum, map_smul, smul_eq_mul, mul_assoc]
    exact Finset.sum_congr rfl (fun p _ => (hphase p).symm)
  have hh := (φ.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg φ))
  rwa [heq, RCLike.norm_ofReal,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hh

theorem infinity_weighted_norm_summable
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) :
    Summable (fun p : ℕ × ℕ =>
      ‖x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜)))‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (infinity_weighted_finite_sum_le φ x)

theorem infinity_weighted_tsum_norm_le
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) :
    (∑' p : ℕ × ℕ, ‖x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜)))‖) ≤
      ‖φ‖ * ‖x‖ :=
  (infinity_weighted_norm_summable φ x).tsum_le_of_sum_le (infinity_weighted_finite_sum_le φ x)

def infinityMatrixFunctional
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜) :
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous {
    toFun := fun x => ∑' p : ℕ × ℕ, x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜)))
    map_add' := by
      intro x y
      simp only [add_apply, lp.coeFn_add, Pi.add_apply, add_mul]
      exact (infinity_weighted_norm_summable φ x).of_norm.tsum_add
        (infinity_weighted_norm_summable φ y).of_norm
    map_smul' := by
      intro a x
      simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact tsum_mul_left }
    ‖φ‖ (fun x => (norm_tsum_le_tsum_norm (infinity_weighted_norm_summable φ x)).trans
      (infinity_weighted_tsum_norm_le φ x))

theorem infinityMatrixFunctional_apply
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜)
    (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) :
    infinityMatrixFunctional φ x = ∑' p : ℕ × ℕ,
      x p.1 p.2 * φ (single p.1 (lp.single ∞ p.2 (1 : 𝕜))) := rfl

theorem infinityMatrixFunctional_single
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜) (r s : ℕ) :
    infinityMatrixFunctional φ (single r (lp.single ∞ s (1 : 𝕜))) =
      φ (single r (lp.single ∞ s (1 : 𝕜))) := by
  classical
  rw [infinityMatrixFunctional_apply, tsum_eq_single (r, s)]
  · simp only [single_apply, ↓reduceIte, lp.single_apply_self, one_mul]
  · intro p hp
    by_cases hr : p.1 = r
    · have hs : p.2 ≠ s := fun hs => hp (Prod.ext hr hs)
      simp only [single_apply, if_pos hr, lp.single_apply, Pi.single_apply, if_neg hs, zero_mul]
    · simp only [single_apply, if_neg hr, lp.coeFn_zero, Pi.zero_apply, zero_mul]

theorem infinityMatrixFunctional_norm_le
    (φ : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜) :
    ‖infinityMatrixFunctional φ‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end SchauderSum
end ThesisCommon
