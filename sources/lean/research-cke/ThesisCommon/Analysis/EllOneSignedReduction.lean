import ThesisCommon.Analysis.LpRestrictedAveraging

/-! Signed averaging for the additive ell1 target norm. This is the common
estimate in UPFP Lemmas 3.2 and 4.4, before supplying the actual blocks. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem sign_projected_sum_le {n : ℕ} (R : Fin n → W →L[𝕜] Y)
    (hR : ∀ w, (∑ i, ‖R i w‖) ≤ ‖w‖) (x : Fin n → W) {M : ℝ}
    (hsign : ∀ θ : Fin n → Bool, ‖∑ i, signedValue (θ i) (x i)‖ ≤ M) :
    (∑ i, ‖R i (x i)‖) ≤ M := by
  let c : ℝ := Fintype.card (Fin n → Bool)
  have hc : 0 < c := by dsimp [c]; positivity
  have hrow (i : Fin n) : ‖R i (x i)‖ ≤ c⁻¹ *
      ∑ θ : Fin n → Bool, ‖R i (∑ j, signedValue (θ j) (x j))‖ := by
    simpa only [map_sum, signedValue, apply_ite, map_neg] using
      norm_le_sign_average (𝕜 := 𝕜) (fun j => R i (x j)) i
  calc
    _ ≤ ∑ i : Fin n, c⁻¹ * ∑ θ : Fin n → Bool,
        ‖R i (∑ j, signedValue (θ j) (x j))‖ := Finset.sum_le_sum (fun i _ => hrow i)
    _ = c⁻¹ * ∑ θ : Fin n → Bool, ∑ i : Fin n,
        ‖R i (∑ j, signedValue (θ j) (x j))‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ c⁻¹ * ∑ _θ : Fin n → Bool, M := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact Finset.sum_le_sum (fun θ _ => (hR _).trans (hsign θ))
    _ = M := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change c⁻¹ * (c * M) = M
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem exists_small_block_of_additive_target {n : ℕ}
    (R : Fin n → W →L[𝕜] Y) (hR : ∀ w, (∑ i, ‖R i w‖) ≤ ‖w‖)
    (J : Fin n → X →L[𝕜] Z) {B : ℝ}
    (hJ : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) → ∀ θ : Fin n → Bool,
      ‖∑ i, signedValue (θ i) (J i (x i))‖ ≤ B)
    (T : Z →L[𝕜] W) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (hlarge : M * B < (n : ℝ) * (ε / 2)) :
    ∃ i : Fin n, ‖((R i).comp T).comp (J i)‖ < ε := by
  classical
  by_contra! hlargeblocks
  have hx : ∀ i : Fin n, ∃ x : X, ‖x‖ < 1 ∧ ε / 2 < ‖R i (T (J i x))‖ := by
    intro i
    exact (((R i).comp T).comp (J i)).exists_lt_apply_of_lt_opNorm
      (by linarith [hlargeblocks i])
  choose x hxnorm hxlarge using hx
  have hsign (θ : Fin n → Bool) : ‖∑ i, signedValue (θ i) (T (J i (x i)))‖ ≤ M * B := by
    have heq : (∑ i, signedValue (θ i) (T (J i (x i)))) =
        T (∑ i, signedValue (θ i) (J i (x i))) := by
      simp only [map_sum, signedValue, apply_ite, map_neg]
    rw [heq]
    exact (T.le_opNorm _).trans (mul_le_mul hT
      (hJ x (fun i => (hxnorm i).le) θ) (norm_nonneg _) hM)
  have hupper := sign_projected_sum_le R hR (fun i => T (J i (x i))) hsign
  have hlower : (n : ℝ) * (ε / 2) ≤ ∑ i : Fin n, ‖R i (T (J i (x i)))‖ := by
    calc
      _ = ∑ _i : Fin n, ε / 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (hxlarge i).le)
  exact (not_lt_of_ge (hlower.trans hupper)) hlarge

theorem ellOne_disjoint_restriction_sum_le (n : ℕ) (x : EllOneSum ℕ X) :
    (∑ i : Fin n, ‖lpRestrict (𝕜 := 𝕜) 1 (disjointCoordinateEmbedding i) x‖) ≤ ‖x‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    lp_disjoint_restriction_rpow_sum_le (𝕜 := 𝕜) 1 (by simp) n x

theorem ellOne_finite_coordinate_sum_le (n : ℕ) (x : EllOneSum (Fin n) X) :
    (∑ i : Fin n, ‖lpCoordinate (𝕜 := 𝕜) 1 i x‖) ≤ ‖x‖ := by
  simpa only [lpCoordinate_apply, ENNReal.toReal_one, Real.rpow_one] using
    lp.sum_rpow_le_norm_rpow (p := 1) (by simp) x Finset.univ

end ThesisCommon
