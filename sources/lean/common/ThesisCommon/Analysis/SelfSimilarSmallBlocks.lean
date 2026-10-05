import ThesisCommon.Analysis.LpRestrictedAveraging
import Mathlib.Data.Fintype.Pigeonhole

/-! UPFP Lemmas 3.7 and 4.8, the finite-p self-similarity one-step estimates.
Disjoint infinite coordinate blocks, signed averaging, Jensen, and finite
pigeonhole supply the actual restrictions. No cotype assumption is used.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem finite_exponent_toReal_ge_one (hp : p ≠ ∞) : 1 ≤ p.toReal := by
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).mpr (Fact.out : 1 ≤ p)

/-- Pigeonhole selects one input block and infinitely many output rows.
The inner coordinate set here can even be chosen constant on those rows. -/
theorem lp_infinite_small_restricted_block (hp : p ≠ ∞) {n : ℕ}
    (J : Fin n → Y →L[𝕜] Z)
    (hJ : ∀ x : Fin n → Y, (∀ i, ‖x i‖ ≤ 1) →
      ∀ θ : Fin n → Bool, ‖∑ i, if θ i then J i (x i) else -(J i (x i))‖ ≤ 1)
    (T : ℕ → Z →L[𝕜] lp (fun _ : ℕ => X) p) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hT : ∀ m, ‖T m‖ ≤ M)
    (hlarge : 2 * M < (n : ℝ) ^ (1 / p.toReal) * ε) :
    ∃ i : Fin n, {m : ℕ | ‖((lpRestrict p (disjointCoordinateEmbedding i)).comp
      (T m)).comp (J i)‖ < ε}.Infinite := by
  classical
  have hp1 := finite_exponent_toReal_ge_one p hp
  have hpower : M ^ p.toReal < (n : ℝ) * (ε / 2) ^ p.toReal := by
    simpa only [Real.one_rpow, one_mul] using cotype_power_threshold
      (zero_lt_one.trans_le hp1) zero_le_one hM (by simpa using hlarge)
  choose i hi using fun m => lp_exists_small_restricted_block p hp1 J hJ
    (T m) hε hM (hT m) hpower
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
  have hj' : (i ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
  refine ⟨j, hj'.mono ?_⟩
  intro m hm
  have heq : i m = j := hm
  simpa only [Set.mem_setOf_eq, heq] using hi m

/-- UPFP 4.8 for bounded input sequences and finite-p output. -/
theorem infinity_to_lp_backward_reduction (hp : p ≠ ∞)
    (T : EllInfinitySum Y →L[𝕜] lp (fun _ : ℕ => X) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a e : ℕ ↪ ℕ, ‖((lpRestrict p a).comp T).comp (lpExtend ∞ e)‖ < ε := by
  have hp1 := finite_exponent_toReal_ge_one p hp
  obtain ⟨n, hn⟩ := exists_cotype_power_threshold (q := p.toReal) (C := 1) (M := ‖T‖) hε
  simp only [Real.one_rpow, one_mul] at hn
  obtain ⟨i, hi⟩ := lp_exists_small_restricted_block p hp1
    (fun i : Fin n => lpExtend (𝕜 := 𝕜) (X := Y) ∞ (disjointCoordinateEmbedding i))
    infinity_disjoint_blocks_sign_bound T hε (norm_nonneg T) le_rfl hn
  exact ⟨disjointCoordinateEmbedding i, disjointCoordinateEmbedding i, hi⟩

/-- UPFP 4.8 for null input sequences and finite-p output. -/
theorem cZero_to_lp_backward_reduction (hp : p ≠ ∞)
    (T : CZeroSum Y →L[𝕜] lp (fun _ : ℕ => X) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a e : ℕ ↪ ℕ, ‖((lpRestrict p a).comp T).comp (cZeroExtend e)‖ < ε := by
  have hp1 := finite_exponent_toReal_ge_one p hp
  obtain ⟨n, hn⟩ := exists_cotype_power_threshold (q := p.toReal) (C := 1) (M := ‖T‖) hε
  simp only [Real.one_rpow, one_mul] at hn
  obtain ⟨i, hi⟩ := lp_exists_small_restricted_block p hp1
    (fun i : Fin n => cZeroExtend (𝕜 := 𝕜) (X := Y) (disjointCoordinateEmbedding i))
    cZero_disjoint_blocks_sign_bound T hε (norm_nonneg T) le_rfl hn
  exact ⟨disjointCoordinateEmbedding i, disjointCoordinateEmbedding i, hi⟩

/-- UPFP 3.7 for bounded output sequences of finite-p sums. -/
theorem infinity_lp_forward_reduction (hp : p ≠ ∞) {n : ℕ}
    (T : lp (fun _ : Fin n => Y) ∞ →L[𝕜] EllInfinitySum (lp (fun _ : ℕ => X) p))
    {ε : ℝ} (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) ^ (1 / p.toReal) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), {m : ℕ | ‖((lpRestrict p a).comp
      ((lpCoordinate ∞ m).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)‖ < ε}.Infinite := by
  have hbound (m : ℕ) : ‖(lpCoordinate ∞ m).comp T‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖lpCoordinate (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p) ∞ m‖ * ‖T‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_lpCoordinate_le ∞ m) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  obtain ⟨i, hi⟩ := lp_infinite_small_restricted_block p hp
    (fun i => lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)
    (fun x hx θ => infinity_single_blocks_sign_bound (𝕜 := 𝕜) x hx θ)
    (fun m => (lpCoordinate ∞ m).comp T) hε (norm_nonneg T) hbound hlarge
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

/-- UPFP 3.7 for null output sequences of finite-p sums. -/
theorem cZero_lp_forward_reduction (hp : p ≠ ∞) {n : ℕ}
    (T : lp (fun _ : Fin n => Y) ∞ →L[𝕜] CZeroSum (lp (fun _ : ℕ => X) p))
    {ε : ℝ} (hε : 0 < ε) (hlarge : 2 * ‖T‖ < (n : ℝ) ^ (1 / p.toReal) * ε) :
    ∃ (i : Fin n) (a : ℕ ↪ ℕ), {m : ℕ | ‖((lpRestrict p a).comp
      ((cZeroCoordinate m).comp T)).comp
        (lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)‖ < ε}.Infinite := by
  have hbound (m : ℕ) : ‖(cZeroCoordinate m).comp T‖ ≤ ‖T‖ := by
    calc
      _ ≤ ‖cZeroCoordinate (𝕜 := 𝕜) (X := lp (fun _ : ℕ => X) p) m‖ * ‖T‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right (norm_cZeroCoordinate_le m) (norm_nonneg T)
      _ = ‖T‖ := one_mul _
  obtain ⟨i, hi⟩ := lp_infinite_small_restricted_block p hp
    (fun i => lp.singleContinuousLinearMap 𝕜 (fun _ : Fin n => Y) ∞ i)
    (fun x hx θ => infinity_single_blocks_sign_bound (𝕜 := 𝕜) x hx θ)
    (fun m => (cZeroCoordinate m).comp T) hε (norm_nonneg T) hbound hlarge
  exact ⟨i, disjointCoordinateEmbedding i, hi⟩

end ThesisCommon
