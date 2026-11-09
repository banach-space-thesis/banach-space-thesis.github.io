import ThesisCommon.Analysis.EllOneCZeroDiagonalReduction
import ThesisCommon.Analysis.CotypeLowerTriangular

/-! The two results in Section 4 of the author edition of the LPCK paper.
The backward estimate uses the threshold without a factor of two. -/
noncomputable section
open scoped ENNReal BigOperators
namespace LPCK.Printed
open ThesisCommon
set_option maxHeartbeats 1200000

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

private theorem small_ellOne_row {N : ℕ} (J : Fin N → X →L[𝕜] Z)
    {B : ℝ}
    (hJ : ∀ x : Fin N → X, (∀ i, ‖x i‖ ≤ 1) → ∀ θ : Fin N → Bool,
      ‖∑ i, signedValue (θ i) (J i (x i))‖ ≤ B)
    (T : Z →L[𝕜] EllOneSum (Fin N) Y) {ε : ℝ}
    (hlarge : ‖T‖ * B < (N : ℝ) * ε) :
    ∃ i : Fin N, ‖((lpCoordinate 1 i).comp T).comp (J i)‖ ≤ ε := by
  classical
  by_contra! h
  let R (i : Fin N) := lpCoordinate (𝕜 := 𝕜) (X := Y) 1 i
  have hx : ∀ i : Fin N, ∃ x : X, ‖x‖ < 1 ∧ ε < ‖R i (T (J i x))‖ :=
    fun i => (((R i).comp T).comp (J i)).exists_lt_apply_of_lt_opNorm (h i)
  choose x hx₁ hx₂ using hx
  have hs (θ : Fin N → Bool) : ‖∑ i, signedValue (θ i) (T (J i (x i)))‖ ≤ ‖T‖ * B := by
    rw [show (∑ i, signedValue (θ i) (T (J i (x i)))) =
      T (∑ i, signedValue (θ i) (J i (x i))) by
      simp only [map_sum, signedValue, apply_ite, map_neg]]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (hJ x (fun i => (hx₁ i).le) θ) (norm_nonneg _))
  have hu := sign_projected_sum_le R (ellOne_finite_coordinate_sum_le N)
    (fun i => T (J i (x i))) hs
  have hl : (N : ℝ) * ε ≤ ∑ i : Fin N, ‖R i (T (J i (x i)))‖ := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hx₂ i).le)
  exact (not_lt_of_ge (hl.trans hu)) hlarge

/-- LPCK Lemma 4.1, for finite p greater than one. -/
theorem lemma_4_1_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    {N : ℕ} (T : lp (fun _ : ℕ => X) p →L[𝕜] EllOneSum (Fin N) X)
    {ε : ℝ} (hlarge : ‖T‖ < (N : ℝ) ^ ((p.toReal - 1) / p.toReal) * ε) :
    ∃ (i : Fin N) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp T).comp (lpExtend p a)‖ ≤ ε := by
  have hpow := ellOne_power_threshold hp (norm_nonneg T)
    (show 2 * ‖T‖ < (N : ℝ) ^ ((p.toReal - 1) / p.toReal) * (2 * ε) by linarith)
  rw [show 2 * ε / 2 = ε by ring] at hpow
  obtain ⟨i, hi⟩ := small_ellOne_row (Y := X) (X := lp (fun _ : ℕ => X) p) (Z := lp (fun _ : ℕ => X) p)
    (fun i : Fin N => lpExtend (𝕜 := 𝕜) (X := X) p (disjointCoordinateEmbedding i))
    (B := (N : ℝ) ^ (1 / p.toReal))
    (fun x hx θ => lp_disjoint_blocks_sign_bound (𝕜 := 𝕜) p (zero_lt_one.trans hp) x hx θ)
    T hpow
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

/-- LPCK Lemma 4.1, for an ℓ∞ domain. -/
theorem lemma_4_1_infinity {N : ℕ}
    (T : EllInfinitySum X →L[𝕜] EllOneSum (Fin N) X) {ε : ℝ}
    (hlarge : ‖T‖ < (N : ℝ) * ε) :
    ∃ (i : Fin N) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp T).comp (lpExtend ∞ a)‖ ≤ ε := by
  obtain ⟨i, hi⟩ := small_ellOne_row (Y := X) (X := EllInfinitySum X) (Z := EllInfinitySum X)
    (fun i : Fin N => lpExtend (𝕜 := 𝕜) (X := X) ∞ (disjointCoordinateEmbedding i))
    (B := 1) (fun x hx θ => infinity_disjoint_blocks_sign_bound (𝕜 := 𝕜) x hx θ) T
    (by simpa only [mul_one] using hlarge)
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

/-- LPCK Lemma 4.1, for a c₀ domain. -/
theorem lemma_4_1_cZero {N : ℕ}
    (T : CZeroSum X →L[𝕜] EllOneSum (Fin N) X) {ε : ℝ}
    (hlarge : ‖T‖ < (N : ℝ) * ε) :
    ∃ (i : Fin N) (a : ℕ ↪ ℕ), ‖((lpCoordinate 1 i).comp T).comp (cZeroExtend a)‖ ≤ ε := by
  obtain ⟨i, hi⟩ := small_ellOne_row (Y := X) (X := CZeroSum X) (Z := CZeroSum X)
    (fun i : Fin N => cZeroExtend (𝕜 := 𝕜) (X := X) (disjointCoordinateEmbedding i))
    (B := 1) (fun x hx θ => cZero_disjoint_blocks_sign_bound (𝕜 := 𝕜) x hx θ) T
    (by simpa only [mul_one] using hlarge)
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

private theorem diagonal_is_lower (S : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) :
    IsLpLowerPart (lpDiagonalPart S) (lpDiagonalPart S) := by
  intro x k
  simp [lpDiagonalPart_apply, lpPrefix_apply]

/-- LPCK Proposition 4.2. The chosen lower triangular operator can even be diagonal. -/
theorem proposition_4_2_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = ∞ ∨ 1 < p.toReal)
    (T : EllOneSum ℕ (lp (fun _ : ℕ => X) p) →L[𝕜]
      EllOneSum ℕ (lp (fun _ : ℕ => X) p)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ) (L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X),
      StrictMono n ∧ StrictMono m ∧ IsLpLowerPart L L ∧
        ‖((lpPointRead p 1 n m).comp T).comp (lpPointInsert p 1 n m) - L‖ < ε := by
  obtain ⟨n, m, hn, hm, h⟩ := ellOne_lp_diagonal_reduction p hp T hε
  exact ⟨n, m, _, hn, hm, diagonal_is_lower _, h⟩

/-- LPCK Proposition 4.2 for c₀ coefficients. -/
theorem proposition_4_2_cZero
    (T : EllOneSum ℕ (CZeroSum X) →L[𝕜] EllOneSum ℕ (CZeroSum X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ ↪ ℕ) (m : ℕ → ℕ) (L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X),
      StrictMono n ∧ StrictMono m ∧ IsLpLowerPart L L ∧
        ‖((lpCZeroPointRead 1 n m).comp T).comp (lpCZeroPointInsert 1 n m) - L‖ < ε := by
  obtain ⟨n, m, hn, hm, h⟩ := ellOne_cZero_diagonal_reduction T hε
  exact ⟨n, m, _, hn, hm, diagonal_is_lower _, h⟩

end LPCK.Printed
