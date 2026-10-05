import ThesisCommon.Analysis.NormingSequence
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace ThesisCommon
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def transportedNorming (T : E ≃L[ℝ] F) (e : ℕ → F →L[ℝ] ℝ) : ℕ → E →L[ℝ] ℝ :=
  fun n => (max 1 ‖T.toContinuousLinearMap‖)⁻¹ • (e n).comp T.toContinuousLinearMap

@[simp] theorem transportedNorming_apply (T : E ≃L[ℝ] F) (e : ℕ → F →L[ℝ] ℝ)
    (n : ℕ) (x : E) : transportedNorming T e n x =
      (max 1 ‖T.toContinuousLinearMap‖)⁻¹ * e n (T x) := rfl

theorem transportedNorming_isNorming (T : E ≃L[ℝ] F) {e : ℕ → F →L[ℝ] ℝ}
    (he : IsNorming e) : IsNorming (transportedNorming T e) := by
  obtain ⟨c, hc, hc1, heunit, helower⟩ := he
  let K := max 1 ‖T.toContinuousLinearMap‖
  let M := max 1 ‖T.symm.toContinuousLinearMap‖
  have hK1 : 1 ≤ K := le_max_left _ _
  have hM1 : 1 ≤ M := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hKM : 0 < K * M := mul_pos hK hM
  have hKM1 : 1 ≤ K * M := by nlinarith
  have hTx (x : E) : ‖T x‖ ≤ K * ‖x‖ :=
    (T.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))
  have hunit (n) : ‖transportedNorming T e n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [transportedNorming_apply, norm_mul, Real.norm_eq_abs K⁻¹,
      abs_of_nonneg (inv_nonneg.mpr hK.le), one_mul]
    have hn : ‖e n (T x)‖ ≤ ‖T x‖ := by
      have h := (e n).le_opNorm (T x)
      exact h.trans (by simpa using mul_le_mul_of_nonneg_right (heunit n) (norm_nonneg (T x)))
    have h := mul_le_mul_of_nonneg_left (hn.trans (hTx x)) (inv_nonneg.mpr hK.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul] using h
  refine ⟨c / (K * M), div_pos hc hKM, (div_le_one hKM).mpr (hc1.trans hKM1), hunit, ?_⟩
  intro x
  have hb := evaluations_bddAbove _ hunit x
  have hsup : (⨆ n, |e n (T x)|) ≤ K * (⨆ n, |transportedNorming T e n x|) := by
    apply ciSup_le
    intro n
    have hn := mul_le_mul_of_nonneg_left (le_ciSup hb n) hK.le
    have heq : K * |transportedNorming T e n x| = |e n (T x)| := by
      rw [transportedNorming_apply, abs_mul, abs_of_pos (inv_pos.mpr hK)]
      change K * (K⁻¹ * |e n (T x)|) = _
      rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    rwa [heq] at hn
  have hx : ‖x‖ ≤ M * ‖T x‖ := by
    have h := T.symm.toContinuousLinearMap.le_opNorm (T x)
    change ‖T.symm (T x)‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T x‖ at h
    rw [T.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg (T x)))
  have h1 := mul_le_mul_of_nonneg_left hx hc.le
  have h2 := mul_le_mul_of_nonneg_left ((helower (T x)).trans hsup) hM.le
  rw [div_mul_eq_mul_div, div_le_iff₀ hKM]
  nlinarith

/-- DP, including its quantification over norming sequences, is invariant under Banach isomorphism. -/
theorem not_desiredProperty_of_equiv (T : E ≃L[ℝ] F) (hF : ¬ DesiredProperty F) :
    ¬ DesiredProperty E := by
  obtain ⟨e, he, hmod⟩ := (not_desiredProperty_iff (E := F)).mp hF
  apply (not_desiredProperty_iff (E := E)).mpr
  refine ⟨transportedNorming T e, transportedNorming_isNorming T he, ?_⟩
  intro f
  obtain ⟨g, hg⟩ := hmod (T f)
  refine ⟨T.symm g, fun n => ?_⟩
  rw [transportedNorming_apply, transportedNorming_apply, T.apply_symm_apply, hg n, abs_mul]
  rw [abs_of_nonneg (show 0 ≤ (max 1 ‖T.toContinuousLinearMap‖)⁻¹ from
    inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _)))]

theorem desiredProperty_equiv (T : E ≃L[ℝ] F) : DesiredProperty E ↔ DesiredProperty F := by
  constructor
  · intro hE
    by_contra hF
    exact not_desiredProperty_of_equiv T hF hE
  · intro hF
    by_contra hE
    exact not_desiredProperty_of_equiv T.symm hE hF

end ThesisCommon
