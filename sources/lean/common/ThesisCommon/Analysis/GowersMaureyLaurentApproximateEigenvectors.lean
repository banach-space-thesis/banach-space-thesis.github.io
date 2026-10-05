import ThesisCommon.Analysis.GowersMaureyGeometricBlocks
import ThesisCommon.Analysis.GowersMaureyShiftEigenEstimates
import ThesisCommon.Analysis.GowersMaureySpreadLaurentReduction
import ThesisCommon.Analysis.WienerCharacters

/-! Absolutely summable Laurent synthesis preserves approximate shift
eigenvectors. Finite-coordinate approximation controls the Wiener tail in
operator norm; no first moment of the coefficients is required. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon.GowersMaurey

theorem laurent_eigen_error_le_two_norm (D : ConstructionData ℂ)
    (a : WienerSequences ℂ) (z : Circle) (x : ShiftSpace D) :
    ‖laurentOperator D a x-wienerEvaluate z a • x‖ ≤ 2*‖a‖*‖x‖ := by
  have hA : ‖laurentOperator D a x‖ ≤ ‖a‖*‖x‖ := by
    have hn : ‖laurentOperator D a‖ ≤ ‖a‖ := ((laurentOperator D).le_opNorm a).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_laurentOperator_le D) (norm_nonneg a))
    exact ((laurentOperator D a).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg x))
  have he : ‖wienerEvaluate z a‖ ≤ ‖a‖ := ((wienerEvaluate z).le_opNorm a).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_wienerEvaluate_le z) (norm_nonneg a))
  have hh := norm_sub_le (laurentOperator D a x) (wienerEvaluate z a • x)
  rw [norm_smul] at hh
  nlinarith [mul_le_mul_of_nonneg_right he (norm_nonneg x)]

theorem finite_laurent_eigen_error_le (D : ConstructionData ℂ) (s : Finset ℤ)
    (a : ℤ → ℂ) (z : Circle) (x : ShiftSpace D) :
    ‖laurentOperator D (∑ d ∈ s, lp.single 1 d (a d)) x -
      wienerEvaluate z (∑ d ∈ s, lp.single 1 d (a d)) • x‖ ≤
      (∑ d ∈ s, ‖a d‖*(d.natAbs : ℝ)) *
        ‖completedSpread D 0 1 x-(z : ℂ) • x‖ := by
  have he : laurentOperator D (∑ d ∈ s, lp.single 1 d (a d)) x -
      wienerEvaluate z (∑ d ∈ s, lp.single 1 d (a d)) • x =
      ∑ d ∈ s, a d • (integerShift D d x-(z : ℂ)^d • x) := by
    simp only [map_sum, laurentOperator_single_scalar, wienerEvaluate_single,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      Finset.sum_smul, smul_sub, smul_smul, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ d ∈ s, ‖a d • (integerShift D d x-(z : ℂ)^d • x)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ s, ‖a d‖*((d.natAbs : ℝ)*‖completedSpread D 0 1 x-(z : ℂ) • x‖) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (integerShift_eigen_error_le D (Circle.norm_coe z) x d)
        (norm_nonneg _)
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

theorem exists_laurent_eigen_error_control (D : ConstructionData ℂ)
    (a : WienerSequences ℂ) (z : Circle) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ShiftSpace D, ‖x‖ = 1 →
      ‖completedSpread D 0 1 x-(z : ℂ) • x‖ < δ →
      ‖laurentOperator D a x-wienerEvaluate z a • x‖ < ε := by
  classical
  obtain ⟨s,hs⟩ := ((lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a).eventually
    (Metric.ball_mem_nhds a (show 0 < ε/8 by positivity))).exists
  let b : WienerSequences ℂ := ∑ d ∈ s, lp.single 1 d (a d)
  have hab : ‖a-b‖ < ε/8 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, b] using hs
  let C : ℝ := ∑ d ∈ s, ‖a d‖*(d.natAbs : ℝ)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity))
  let δ := ε/(4*(C+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro x hx hshift
  have hb := finite_laurent_eigen_error_le D s a z x
  change ‖laurentOperator D b x-wienerEvaluate z b • x‖ ≤
    C*‖completedSpread D 0 1 x-(z : ℂ) • x‖ at hb
  have hbudget : C*δ ≤ ε/4 := by
    calc
      C*δ ≤ (C+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε/4 := by dsimp only [δ]; field_simp
  have hb' : ‖laurentOperator D b x-wienerEvaluate z b • x‖ ≤ ε/4 :=
    hb.trans ((mul_le_mul_of_nonneg_left hshift.le hC).trans hbudget)
  have hr := laurent_eigen_error_le_two_norm D (a-b) z x
  rw [hx, mul_one] at hr
  have he : laurentOperator D a x-wienerEvaluate z a • x =
      (laurentOperator D (a-b) x-wienerEvaluate z (a-b) • x)+
      (laurentOperator D b x-wienerEvaluate z b • x) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply, sub_smul]
    abel
  rw [he]
  have hh := norm_add_le (laurentOperator D (a-b) x-wienerEvaluate z (a-b) • x)
    (laurentOperator D b x-wienerEvaluate z b • x)
  linarith

theorem exists_unit_tail_laurent_approximate_eigenvector (D : ConstructionData ℂ)
    (a : WienerSequences ℂ) (z : Circle) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : C00 ℂ, x ∈ afterCutoff B ∧ implicitNorm D x = 1 ∧
      ‖laurentOperator D a (denseEmbedding D x)-wienerEvaluate z a • denseEmbedding D x‖ < ε := by
  obtain ⟨δ,hδ,hcontrol⟩ := exists_laurent_eigen_error_control D a z hε
  have hz : ‖(z : ℂ)⁻¹‖ = 1 := by simp
  obtain ⟨x,hxB,hxn,hxs⟩ := exists_unit_tail_shift_approximate_eigenvector D hz B hδ
  refine ⟨x,hxB,hxn,hcontrol (denseEmbedding D x) ?_ ?_⟩
  · simpa only [denseEmbedding_norm] using hxn
  · rw [completedSpread_denseEmbedding, ← map_smul, ← map_sub, denseEmbedding_norm]
    simpa only [inv_inv] using hxs

end ThesisCommon.GowersMaurey
