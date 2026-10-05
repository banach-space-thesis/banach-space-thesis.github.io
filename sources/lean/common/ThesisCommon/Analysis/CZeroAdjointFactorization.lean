import ThesisCommon.Analysis.CZeroDualEllOne
import ThesisCommon.Analysis.HahnBanachBoundedBelow
import ThesisCommon.Analysis.LpOneColumnsOperator
import ThesisCommon.Analysis.BanachAdjointNorm
import ThesisCommon.Analysis.WeakEssentialFactorizationBound

/-! A quantitatively bounded-below c0 restriction gives a genuine ell-one
identity factorization through the Banach adjoint. Coordinate functionals
are extended by Hahn–Banach and assembled by absolute summation. -/
noncomputable section
set_option maxSynthPendingDepth 3
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_ellOne_factorization_adjoint_of_cZero_lower_bound
    (T : E →L[𝕜] F) (V : CZeroSum 𝕜 →L[𝕜] E)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ x, c * ‖x‖ ≤ ‖T (V x)‖) :
    ∃ U : (E →L[𝕜] 𝕜) →L[𝕜] lp (fun _ : ℕ => 𝕜) 1,
      ∃ R : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] (F →L[𝕜] 𝕜),
        U.comp ((banachAdjoint T).comp R) = ContinuousLinearMap.id 𝕜 _ ∧
        ‖U‖ ≤ ‖V‖ ∧ ‖R‖ ≤ c⁻¹ := by
  classical
  choose ψ hψ hψnorm using fun n : ℕ =>
    exists_dual_extension_along_lower_bound (T.comp V) hc hlower
      (cZeroCoordinate (𝕜 := 𝕜) (X := 𝕜) n)
  have hψbound (n : ℕ) : ‖ψ n‖ ≤ c⁻¹ := by
    exact (hψnorm n).trans ((mul_le_mul_of_nonneg_left (norm_cZeroCoordinate_le n)
      (inv_nonneg.mpr hc.le)).trans_eq (mul_one _))
  let R := lpOneColumnsOperator (𝕜 := 𝕜) ψ c⁻¹ (inv_nonneg.mpr hc.le) hψbound
  have hR : ‖R‖ ≤ c⁻¹ := norm_lpOneColumnsOperator_le ψ _ _ _
  have hRs (n : ℕ) : R (lp.single 1 n 1) = ψ n := by
    have h := lpOneColumnsOperator_single (𝕜 := 𝕜) ψ c⁻¹ (inv_nonneg.mpr hc.le) hψbound n
    convert h using 1
    congr 1
    apply lp.ext
    funext j
    by_cases hj : j = n <;> simp [lp.single_apply, hj]
  let U := (cZeroDualToEllOne (𝕜 := 𝕜)).comp (banachAdjoint V)
  have hU : ‖U‖ ≤ ‖V‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right
      norm_cZeroDualToEllOne_le (norm_nonneg (banachAdjoint V))).trans_eq
      (by rw [one_mul, norm_banachAdjoint]))
  have hs (n : ℕ) : U (banachAdjoint T (R (lp.single 1 n 1))) = lp.single 1 n 1 := by
    rw [hRs]
    apply lp.ext
    funext j
    change ψ n (T (V (cZeroSingle j 1))) = lp.single (E := fun _ : ℕ => 𝕜) 1 n 1 j
    have h := congrArg (fun φ : CZeroSum 𝕜 →L[𝕜] 𝕜 => φ (cZeroSingle j 1)) (hψ n)
    change ψ n (T (V (cZeroSingle j 1))) = cZeroSingle j (1 : 𝕜) n at h
    rw [h]
    by_cases hj : j = n
    · subst j
      simp
    · rw [lp.single_apply_ne 1 n 1 hj]
      simp [cZeroSingle_apply, Ne.symm hj]
  refine ⟨U, R, ?_, hU, hR⟩
  apply lp.ext_continuousLinearMap (by simp)
  intro n
  apply ContinuousLinearMap.ext
  intro a
  change U (banachAdjoint T (R (lp.single 1 n a))) = lp.single 1 n a
  have ha : (lp.single 1 n a : lp (fun _ : ℕ => 𝕜) 1) = a • lp.single 1 n 1 := by
    rw [← lp.single_smul]
    simp
  simp only [ha, map_smul, hs]

theorem cZero_lower_bound_le_adjoint_weakEssentialNorm
    (T : E →L[𝕜] F) (V : CZeroSum 𝕜 →L[𝕜] E) (hV : ‖V‖ ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (hlower : ∀ x, c * ‖x‖ ≤ ‖T (V x)‖) :
    c ≤ weakEssentialNorm (banachAdjoint T) := by
  rcases hc.eq_or_lt with rfl | hc
  · exact weakEssentialNorm_nonneg _
  obtain ⟨U, R, hfactor, hU, hR⟩ :=
    exists_ellOne_factorization_adjoint_of_cZero_lower_bound T V hc hlower
  have h := weakEssentialNorm_id_le_factorization_norms (banachAdjoint T) U R hfactor
  rw [weakEssentialNorm_id_scalarEllOne] at h
  have hUR : ‖U‖ * ‖R‖ ≤ c⁻¹ := by
    exact (mul_le_mul (hU.trans hV) hR (norm_nonneg R) zero_le_one).trans_eq (one_mul _)
  have hmain : 1 ≤ c⁻¹ * weakEssentialNorm (banachAdjoint T) :=
    h.trans (mul_le_mul_of_nonneg_right hUR (weakEssentialNorm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hmain hc.le
  simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hh

end ThesisCommon
