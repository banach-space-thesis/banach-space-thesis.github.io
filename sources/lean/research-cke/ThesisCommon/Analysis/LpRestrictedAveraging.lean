import ThesisCommon.Analysis.SignAveraging
import ThesisCommon.Analysis.LpSelfSimilarity
import ThesisCommon.Analysis.CotypeEstimates
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! The signed averaging estimate behind UPFP Lemmas 3.7 and 4.8.
Disjoint target blocks contribute additively to the finite-p power of the
norm. Sign orthogonality and Jensen extract each matching input block.
No cotype assumption on the coefficient space is used here.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem lp_disjoint_restriction_rpow_sum_le (hp : 0 < p.toReal) (n : ℕ)
    (x : lp (fun _ : ℕ => X) p) :
    (∑ i : Fin n, ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x‖ ^ p.toReal)
      ≤ ‖x‖ ^ p.toReal := by
  have h := lp.sum_rpow_le_norm_rpow hp
    (lpFiniteUnflattenValue (𝕜 := 𝕜) p hp x) (Finset.range n)
  rw [norm_lpFiniteUnflattenValue] at h
  change (∑ i ∈ Finset.range n,
    ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x‖ ^ p.toReal) ≤ ‖x‖ ^ p.toReal at h
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) x‖ ^ p.toReal)]
  exact h

/-- Extract all matching disjoint blocks from a uniformly bounded signed sum. -/
theorem lp_restricted_sign_bound (hp : 1 ≤ p.toReal) {n : ℕ}
    (x : Fin n → lp (fun _ : ℕ => X) p) {M : ℝ}
    (hsign : ∀ θ : Fin n → Bool, ‖∑ j, signedValue (θ j) (x j)‖ ≤ M) :
    (∑ i : Fin n, ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) (x i)‖ ^ p.toReal)
      ≤ M ^ p.toReal := by
  let c : ℝ := Fintype.card (Fin n → Bool)
  have hc : 0 < c := by dsimp [c]; positivity
  have hrow (i : Fin n) :
      ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) (x i)‖ ^ p.toReal ≤
        c⁻¹ * ∑ θ : Fin n → Bool,
          ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i)
            (∑ j, signedValue (θ j) (x j))‖ ^ p.toReal := by
    have h := norm_rpow_le_sign_average (𝕜 := 𝕜)
      (fun j => lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) (x j)) i hp
    simpa only [map_sum, signedValue, apply_ite, map_neg] using h
  calc
    _ ≤ ∑ i : Fin n, c⁻¹ * ∑ θ : Fin n → Bool,
        ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i)
          (∑ j, signedValue (θ j) (x j))‖ ^ p.toReal :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = c⁻¹ * ∑ θ : Fin n → Bool, ∑ i : Fin n,
        ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i)
          (∑ j, signedValue (θ j) (x j))‖ ^ p.toReal := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ c⁻¹ * ∑ _θ : Fin n → Bool, M ^ p.toReal := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      apply Finset.sum_le_sum
      intro θ _
      exact (lp_disjoint_restriction_rpow_sum_le p (zero_lt_one.trans_le hp) n _).trans
        (Real.rpow_le_rpow (norm_nonneg _) (hsign θ) (zero_le_one.trans hp))
    _ = M ^ p.toReal := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change c⁻¹ * (c * M ^ p.toReal) = M ^ p.toReal
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Operator form: at least one matching pair of blocks is small under the
manuscript's equivalent pth-power threshold. -/
theorem lp_exists_small_restricted_block (hp : 1 ≤ p.toReal) {n : ℕ}
    (J : Fin n → Y →L[𝕜] Z)
    (hJ : ∀ x : Fin n → Y, (∀ i, ‖x i‖ ≤ 1) →
      ∀ θ : Fin n → Bool, ‖∑ i, if θ i then J i (x i) else -(J i (x i))‖ ≤ 1)
    (T : Z →L[𝕜] lp (fun _ : ℕ => X) p) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M)
    (hlarge : M ^ p.toReal < (n : ℝ) * (ε / 2) ^ p.toReal) :
    ∃ i : Fin n,
      ‖((lpRestrict p (disjointCoordinateEmbedding i)).comp T).comp (J i)‖ < ε := by
  classical
  by_contra! hlargeblocks
  have hx : ∀ i : Fin n, ∃ x : Y, ‖x‖ < 1 ∧ ε / 2 <
      ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i) (T (J i x))‖ := by
    intro i
    exact (((lpRestrict p (disjointCoordinateEmbedding i)).comp T).comp (J i)).exists_lt_apply_of_lt_opNorm
      (by linarith [hlargeblocks i])
  choose x hxnorm hxlarge using hx
  have hsign (θ : Fin n → Bool) : ‖∑ i, signedValue (θ i) (T (J i (x i)))‖ ≤ M := by
    have heq : (∑ i, signedValue (θ i) (T (J i (x i)))) =
        T (∑ i, if θ i then J i (x i) else -(J i (x i))) := by
      simp only [map_sum, signedValue, apply_ite, map_neg]
    rw [heq]
    calc
      _ ≤ ‖T‖ * ‖∑ i, if θ i then J i (x i) else -(J i (x i))‖ := T.le_opNorm _
      _ ≤ M * 1 := mul_le_mul hT (hJ x (fun i => (hxnorm i).le) θ) (norm_nonneg _) hM
      _ = M := mul_one M
  have hupper := lp_restricted_sign_bound (𝕜 := 𝕜) p hp (fun i => T (J i (x i))) hsign
  have hlower : (n : ℝ) * (ε / 2) ^ p.toReal ≤
      ∑ i : Fin n, ‖lpRestrict (𝕜 := 𝕜) p (disjointCoordinateEmbedding i)
        (T (J i (x i)))‖ ^ p.toReal := by
    calc
      _ = ∑ _i : Fin n, (ε / 2) ^ p.toReal := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (half_pos hε).le
        (hxlarge i).le (zero_le_one.trans hp))
  exact (not_lt_of_ge (hlower.trans hupper)) hlarge

end ThesisCommon
