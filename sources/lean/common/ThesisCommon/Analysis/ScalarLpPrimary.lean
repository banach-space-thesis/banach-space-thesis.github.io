import ThesisCommon.Analysis.ScalarLpBackward
import ThesisCommon.Analysis.ScalarSequencePrimary
import ThesisCommon.Analysis.CompactUpperTriangular
import ThesisCommon.Analysis.TriangularDiagonalAlgebra
import ThesisCommon.Analysis.DiagonalAssembly

/-! Scalar sequence spaces have UPFP and are primary for every Banach
exponent. The finite-exponent proof uses the paper's upper/lower reduction,
with compactness of operators whose domain is the scalar field. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem scalar_upper_diagonal_reduction (hp : 1 < p.toReal)
    (U : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p)
    (hU : IsLpUpperPart U U) {ε : ℝ} (hε : 0 < ε) :
    ∃ A B : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p,
      A.comp B = ContinuousLinearMap.id 𝕜 _ ∧ ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ‖(A.comp U).comp B - lpDiagonalPart ((A.comp U).comp B)‖ < ε := by
  obtain ⟨e, L, he, hsmall, hL⟩ := scalar_lp_lower_triangular hp U hε
  have hupper := hU.block_compression e he
    (fun _ => ContinuousLinearMap.id 𝕜 𝕜) (fun _ => ContinuousLinearMap.id 𝕜 𝕜)
    (fun _ => ContinuousLinearMap.norm_id_le) (fun _ => ContinuousLinearMap.norm_id_le)
  simp only [lpBlockRead_id, lpBlockInsert_id] at hupper
  have hdiag := hL.eq_diagonal_of_upper hupper
  refine ⟨lpRestrict p e, lpExtend p e, lpRestrict_comp_extend e,
    norm_lpRestrict_le e, norm_lpExtend_le e, ?_⟩
  rwa [hdiag] at hsmall

theorem scalar_lp_upper_dichotomy (hp : 1 < p.toReal)
    (U : lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p)
    (hU : IsLpUpperPart U U) :
    FactorsIdentityWith U (lp (fun _ : ℕ => 𝕜) p) 4 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 _ - U)
        (lp (fun _ : ℕ => 𝕜) p) 4 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num]
  apply factorization_dichotomy_of_approximate_compressions (by norm_num : (1 : ℝ) ≤ 2)
    U IsLpDiagonal (fun D hD => lp_diagonal_dichotomy (by norm_num) scalar_hasCPFP D hD)
  intro ε hε
  obtain ⟨A, B, hAB, hA, hB, hsmall⟩ := scalar_upper_diagonal_reduction hp U hU hε
  exact ⟨A, B, lpDiagonalPart ((A.comp U).comp B), hAB, hA, hB,
    isLpDiagonal_lpDiagonalPart _, hsmall⟩

theorem scalar_domain_isCompactOperator {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] (S : 𝕜 →L[𝕜] Y) : IsCompactOperator S := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact S.toLinearMap
    (by norm_num : (0 : ℝ) < 1)).2
  exact ⟨S '' Metric.closedBall 0 1, (isCompact_closedBall (0 : 𝕜) 1).image S.continuous,
    Set.Subset.rfl⟩

theorem scalar_lp_finite_hasCPFP (hp : p ≠ ∞) (hp1 : 1 < p.toReal) :
    HasCPFP 𝕜 (lp (fun _ : ℕ => 𝕜) p) 8 := by
  rw [show (8 : ℝ) = 2 * 4 by norm_num]
  apply hasCPFP_of_approximate_compressions (by norm_num : (1 : ℝ) ≤ 4)
    (fun U => IsLpUpperPart U U) (fun U hU => scalar_lp_upper_dichotomy hp1 U hU)
  intro T ε hε
  obtain ⟨e, U, _, hsmall, hU⟩ := lp_upper_triangular_of_scalar_compact hp
    (fun S => scalar_domain_isCompactOperator S) T hε
  exact ⟨lpRestrict p e, lpExtend p e, U, lpRestrict_comp_extend e,
    norm_lpRestrict_le e, norm_lpExtend_le e, hU.self_upperPart, hsmall⟩

theorem scalar_lp_hasUPFP (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HasUPFP 𝕜 (lp (fun _ : ℕ => 𝕜) p) := by
  by_cases hp : p = ∞
  · subst p
    exact scalar_infinity_hasUPFP
  by_cases hp1 : p = 1
  · subst p
    exact scalar_ellOne_hasUPFP
  have hlt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) (Ne.symm hp1)
  have hreal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) hp).mpr hlt
  exact ⟨8, by norm_num, scalar_lp_finite_hasCPFP hp hreal⟩

theorem scalar_lp_isPrimary (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsPrimary 𝕜 (lp (fun _ : ℕ => 𝕜) p) :=
  (scalar_lp_hasUPFP p).lp_isPrimary

end ThesisCommon
