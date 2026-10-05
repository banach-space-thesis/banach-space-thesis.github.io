import ThesisCommon.Analysis.CZeroAlmostIsometricBlocks
import ThesisCommon.Analysis.CZeroFunctionalRows
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! Quantitative c₀ subcopy extraction from actual column lower bounds.
Hahn–Banach norming functionals and the absolute row estimate make the
near-maximal block map bounded below; no Rosenthal extraction is assumed. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem cZero_lower_bound_of_near_unit_columns
    (V : CZeroSum 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcol : ∀ n, 1-δ ≤ ‖V (cZeroSingle n 1)‖) (x : CZeroSum 𝕜) :
    (1-2*δ)*‖x‖ ≤ ‖V x‖ := by
  classical
  choose φ hφ hφnorm using fun n => exists_dual_vector'' 𝕜 (V (cZeroSingle n 1))
  have hrow (n : ℕ) : ‖(φ n).comp V - cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n‖ ≤ 2*δ := by
    apply cZero_functional_near_coordinate _ n
      (((φ n).opNorm_comp_le V).trans
        ((mul_le_mul (hφ n) hV (norm_nonneg V) zero_le_one).trans_eq (one_mul 1)))
      (norm_nonneg _) _ (hφnorm n) (hcol n)
    exact (V.le_opNorm _).trans
      ((mul_le_mul hV (norm_cZeroSingle_le n (1 : 𝕜))
        (norm_nonneg _) zero_le_one).trans (by simp))
  have hb : ‖x‖ ≤ ‖V x‖+2*δ*‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro n
    have he : ‖φ n (V x) - x n‖ ≤ 2*δ*‖x‖ :=
      (((φ n).comp V - cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hrow n) (norm_nonneg x))
    have hv : ‖φ n (V x)‖ ≤ ‖V x‖ := ((φ n).le_opNorm _).trans
      (by simpa using mul_le_mul_of_nonneg_right (hφ n) (norm_nonneg (V x)))
    have hh := norm_sub_le (φ n (V x)) (φ n (V x)-x n)
    rw [sub_sub_cancel] at hh
    exact hh.trans (add_le_add hv he)
  nlinarith

theorem exists_cZero_subcopy_of_tail_lower_bound (V : CZeroSum 𝕜 →L[𝕜] E)
    {c δ : ℝ} (hc : 0 < c)
    (htail : ∀ n, c ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding n))‖)
    (hδ : 0 < δ) (hδsmall : 2*δ < 1) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ‖A‖ ≤ 1 ∧
      ∀ x, ((1-2*δ)*c)*‖x‖ ≤ ‖V (A x)‖ := by
  letI : NormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] E) :=
    @NormedSpace.toNormSMulClass 𝕜 (CZeroSum 𝕜 →L[𝕜] E) _ _ _
  obtain ⟨A, b, hcb, hA, hVA, hcol⟩ :=
    exists_cZero_almost_maximal_blocks_of_tail_lower_bound V hc htail hδ (by linarith)
  have hb : 0 < b := hc.trans_le hcb
  let U : CZeroSum 𝕜 →L[𝕜] E := ((b⁻¹ : ℝ) : 𝕜) • (V.comp A)
  have hU : ‖U‖ ≤ 1 := by
    dsimp [U]
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    exact (mul_le_mul_of_nonneg_left hVA (inv_nonneg.mpr hb.le)).trans_eq
      (inv_mul_cancel₀ hb.ne')
  have hUc (n : ℕ) : 1-δ ≤ ‖U (cZeroSingle n 1)‖ := by
    change 1-δ ≤ ‖((b⁻¹ : ℝ) : 𝕜) • V (A (cZeroSingle n 1))‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)]
    have h := mul_le_mul_of_nonneg_left (hcol n).le (inv_nonneg.mpr hb.le)
    have heq : b⁻¹ * ((1-δ)*b) = 1-δ := by field_simp
    exact heq.symm.trans_le h
  refine ⟨A, hA, ?_⟩
  intro x
  have h := cZero_lower_bound_of_near_unit_columns U hU hδ.le hUc x
  change (1-2*δ)*‖x‖ ≤ ‖((b⁻¹ : ℝ) : 𝕜) • V (A x)‖ at h
  rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hb)] at h
  have hh := mul_le_mul_of_nonneg_left h hb.le
  rw [← mul_assoc b b⁻¹, mul_inv_cancel₀ hb.ne', one_mul] at hh
  have hcb' := mul_le_mul_of_nonneg_right hcb
    (mul_nonneg (by linarith : 0 ≤ 1-2*δ) (norm_nonneg x))
  nlinarith

theorem cZero_tail_norm_ge_of_column_norm_ge (V : CZeroSum 𝕜 →L[𝕜] E)
    {c : ℝ} (hcol : ∀ n, c ≤ ‖V (cZeroSingle n 1)‖) (p : ℕ) :
    c ≤ ‖V.comp (cZeroExtend (cZeroTailEmbedding p))‖ := by
  have he : ‖cZeroSingle 0 (1 : 𝕜)‖ = 1 := (scalarCZeroSchauderBasis (𝕜 := 𝕜)).norm_vector 0
  have hj : cZeroExtend (𝕜 := 𝕜) (cZeroTailEmbedding p) (cZeroSingle 0 (1 : 𝕜)) =
      cZeroSingle p (1 : 𝕜) := by
    simpa [cZeroTailEmbedding] using
      cZeroExtend_single (𝕜 := 𝕜) (cZeroTailEmbedding p) 0 (1 : 𝕜)
  have hh := (V.comp (cZeroExtend (cZeroTailEmbedding p))).le_opNorm (cZeroSingle 0 1)
  rw [ContinuousLinearMap.comp_apply, hj, he, mul_one] at hh
  exact (hcol p).trans hh

theorem exists_cZero_subcopy_of_column_lower_bound (V : CZeroSum 𝕜 →L[𝕜] E)
    {c ε : ℝ} (hc : 0 < c) (hcol : ∀ n, c ≤ ‖V (cZeroSingle n 1)‖) (hε : 0 < ε) :
    ∃ A : CZeroSum 𝕜 →L[𝕜] CZeroSum 𝕜, ‖A‖ ≤ 1 ∧
      ∀ x, (c-ε)*‖x‖ ≤ ‖V (A x)‖ := by
  let δ := ε/(4*(c+ε))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hden : 0 < 4*(c+ε) := by positivity
  have heq : δ*(4*(c+ε)) = ε := by dsimp [δ]; exact div_mul_cancel₀ _ hden.ne'
  have hdsmall : 2*δ < 1 := by nlinarith
  obtain ⟨A, hA, hlow⟩ := exists_cZero_subcopy_of_tail_lower_bound V hc
    (cZero_tail_norm_ge_of_column_norm_ge V hcol) hd hdsmall
  refine ⟨A, hA, fun x => ?_⟩
  have hcδ : c-ε ≤ (1-2*δ)*c := by nlinarith
  exact (mul_le_mul_of_nonneg_right hcδ (norm_nonneg x)).trans (hlow x)

end ThesisCommon
