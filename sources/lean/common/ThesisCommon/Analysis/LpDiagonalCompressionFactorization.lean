import ThesisCommon.Analysis.LebesgueLpRestrictionAlgebra
import ThesisCommon.Analysis.LpBoundedMultiplier
import ThesisCommon.Analysis.SharpFactorization

/-! A genuine multiplier bounded away from zero on a measurable part supplies
actual factors through every sufficiently close compressed operator. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X] {μ : Measure X}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_lebesgueLp_compression_le_cut (T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)
    (D : Set X) (hD : MeasurableSet D) :
    ‖((lebesgueLpRestrict (𝕜 := 𝕜) D).comp T).comp
      (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) D hD).toContinuousLinearMap‖ ≤
      ‖(lpCutL D hD).comp (T.comp (lpCutL D hD))‖ := by
  let R := lebesgueLpRestrict (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D
  let E := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D hD).toContinuousLinearMap
  let B := (lpCutL D hD).comp (T.comp (lpCutL D hD))
  have hRE : R.comp E = ContinuousLinearMap.id 𝕜 _ := lebesgueLpRestrict_comp_extend D hD
  have hER : E.comp R = lpCutL D hD := lebesgueLpExtend_comp_restrict D hD
  have hnormR : ‖R‖ ≤ 1 := norm_lebesgueLpRestrict_le D
  have hnormE : ‖E‖ ≤ 1 := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) D hD).norm_toContinuousLinearMap_le
  have he : (R.comp T).comp E = (R.comp B).comp E := by
    have hpoint (f : Lp 𝕜 p (μ.restrict D)) : R (E f) = f := DFunLike.congr_fun hRE f
    dsimp only [B]
    rw [← hER]
    ext f : 1
    simp only [ContinuousLinearMap.comp_apply, hpoint]
  change ‖(R.comp T).comp E‖ ≤ ‖B‖
  rw [he]
  calc
    _ ≤ (‖R‖ * ‖B‖) * ‖E‖ := ((R.comp B).opNorm_comp_le E).trans
      (mul_le_mul_of_nonneg_right (R.opNorm_comp_le B) (norm_nonneg E))
    _ ≤ (1 * ‖B‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hnormR (norm_nonneg B)) hnormE (norm_nonneg E) (by positivity)
    _ = ‖B‖ := by ring

theorem factorsIdentityWith_multiplier_part
    (M : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ) (a : X → 𝕜) (ha : Measurable a)
    (hM : ∀ f : Lp 𝕜 p μ, M f =ᵐ[μ] fun x => a x * f x)
    (D : Set X) (hD : MeasurableSet D) (hlower : ∀ x ∈ D, 1 / 2 ≤ ‖a x‖) :
    FactorsIdentityWith (((lebesgueLpRestrict (𝕜 := 𝕜) D).comp M).comp
      (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) D hD).toContinuousLinearMap) (Lp 𝕜 p (μ.restrict D)) 2 := by
  have hinv : ∀ᵐ x ∂μ.restrict D, ‖(a x)⁻¹‖ ≤ (2 : ℝ) := by
    filter_upwards [ae_restrict_mem hD] with x hx
    rw [norm_inv]
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) (hlower x hx)
    norm_num at h ⊢
    exact h
  let U := lpBoundedMultiplier (p := p) (fun x => (a x)⁻¹) ha.inv.aestronglyMeasurable 2 hinv
  let R := lebesgueLpRestrict (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D
  let E := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D hD).toContinuousLinearMap
  refine ⟨U, ContinuousLinearMap.id 𝕜 _, ?_, ?_⟩
  · ext f : 1
    apply Lp.ext
    filter_upwards [lpBoundedMultiplier_coe (p := p) (fun x => (a x)⁻¹)
      ha.inv.aestronglyMeasurable 2 hinv (R (M (E f))),
      lebesgueLpRestrict_coe (𝕜 := 𝕜) D (M (E f)),
      ae_restrict_of_ae (hM (E f)),
      ae_restrict_of_ae (lebesgueLpExtend_coe (𝕜 := 𝕜) D hD f), ae_restrict_mem hD]
      with x hu hr hm he hx
    change U (R (M (E f))) x = f x
    change (E f) x = D.indicator (fun y => f y) x at he
    have hn : a x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlower x hx))
    rw [hu, hr, hm, he, Set.indicator_of_mem hx, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · have hU : ‖U‖ ≤ 2 := norm_lpBoundedMultiplier_le _ _ 2 (by norm_num) hinv
    exact (mul_le_mul hU ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)).trans_eq
      (mul_one 2)

theorem factorsIdentityWith_of_lp_diagonal_compression
    (T M : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ) (a : X → 𝕜) (ha : Measurable a)
    (hM : ∀ f : Lp 𝕜 p μ, M f =ᵐ[μ] fun x => a x * f x)
    (D : Set X) (hD : MeasurableSet D) (hlower : ∀ x ∈ D, 1 / 2 ≤ ‖a x‖)
    (hsmall : ‖(lpCutL D hD).comp ((T - M).comp (lpCutL D hD))‖ ≤ 1 / 4) :
    FactorsIdentityWith T (Lp 𝕜 p (μ.restrict D)) 4 := by
  let R := lebesgueLpRestrict (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D
  let E := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ) D hD).toContinuousLinearMap
  have hbase := factorsIdentityWith_multiplier_part M a ha hM D hD hlower
  have hdiff : ‖(R.comp T).comp E - (R.comp M).comp E‖ ≤ 1 / 4 := by
    rw [← ContinuousLinearMap.sub_comp, ← ContinuousLinearMap.comp_sub]
    exact (norm_lebesgueLp_compression_le_cut (T - M) D hD).trans hsmall
  have hfactor : FactorsIdentityWith ((R.comp T).comp E) (Lp 𝕜 p (μ.restrict D)) 4 := by
    have h := hbase.perturb_fraction (S := (R.comp T).comp E) (r := (1 : ℝ) / 2)
      (by norm_num) (by linarith)
    norm_num at h
    exact h
  apply (hfactor.of_compression R E).mono
  have hR : ‖R‖ ≤ 1 := norm_lebesgueLpRestrict_le D
  have hE : ‖E‖ ≤ 1 := (lebesgueLpExtend (𝕜 := 𝕜) (E := 𝕜) D hD).norm_toContinuousLinearMap_le
  have hprod : ‖R‖ * ‖E‖ ≤ 1 := by
    simpa using mul_le_mul hR hE (norm_nonneg E) zero_le_one
  linarith

end ThesisCommon

