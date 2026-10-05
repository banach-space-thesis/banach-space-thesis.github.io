import Sigma.ComplexDesiredProperty
import Mathlib.Tactic.FieldSimp

/-! Complex desired property is invariant under complex Banach isomorphism.
The rescaling is positive real, which is essential for modulus preservation. -/
noncomputable section
namespace SigmaNonprimarity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexTransportedNorming (T : E ≃L[ℂ] F) (e : ℕ → F →L[ℂ] ℂ) : ℕ → E →L[ℂ] ℂ :=
  fun n => (((max 1 ‖T.toContinuousLinearMap‖)⁻¹ : ℝ) : ℂ) • (e n).comp T.toContinuousLinearMap

@[simp] theorem complexTransportedNorming_apply (T : E ≃L[ℂ] F) (e : ℕ → F →L[ℂ] ℂ)
    (n : ℕ) (x : E) : complexTransportedNorming T e n x =
      (((max 1 ‖T.toContinuousLinearMap‖)⁻¹ : ℝ) : ℂ) * e n (T x) := rfl

theorem complexTransportedNorming_isNorming (T : E ≃L[ℂ] F) {e : ℕ → F →L[ℂ] ℂ}
    (he : IsComplexNorming e) : IsComplexNorming (complexTransportedNorming T e) := by
  obtain ⟨c,hc,hc1,heunit,helower⟩ := he
  let K := max 1 ‖T.toContinuousLinearMap‖
  let M := max 1 ‖T.symm.toContinuousLinearMap‖
  have hK1 : 1 ≤ K := le_max_left _ _
  have hM1 : 1 ≤ M := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hKM : 0 < K*M := mul_pos hK hM
  have hKM1 : 1 ≤ K*M := by nlinarith
  have hTx (x : E) : ‖T x‖ ≤ K*‖x‖ :=
    (T.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))
  have hnorm (n : ℕ) (x : E) : ‖complexTransportedNorming T e n x‖ = K⁻¹*‖e n (T x)‖ := by
    rw [complexTransportedNorming_apply,norm_mul]
    change ‖((K⁻¹ : ℝ) : ℂ)‖ * ‖e n (T x)‖ = _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK)]
  have hunit (n : ℕ) : ‖complexTransportedNorming T e n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [hnorm,one_mul]
    have hn : ‖e n (T x)‖ ≤ ‖T x‖ := ((e n).le_opNorm (T x)).trans (by
      simpa using mul_le_mul_of_nonneg_right (heunit n) (norm_nonneg (T x)))
    have h := mul_le_mul_of_nonneg_left (hn.trans (hTx x)) (inv_nonneg.mpr hK.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hK.ne',one_mul] using h
  refine ⟨c/(K*M),div_pos hc hKM,(div_le_one hKM).mpr (hc1.trans hKM1),hunit,?_⟩
  intro x
  have hb := complex_evaluations_bddAbove _ hunit x
  have hsup : (⨆ n, ‖e n (T x)‖) ≤ K*(⨆ n, ‖complexTransportedNorming T e n x‖) := by
    apply ciSup_le
    intro n
    have hn := mul_le_mul_of_nonneg_left (le_ciSup hb n) hK.le
    rw [hnorm,← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] at hn
    exact hn
  have hx : ‖x‖ ≤ M*‖T x‖ := by
    have h := T.symm.toContinuousLinearMap.le_opNorm (T x)
    change ‖T.symm (T x)‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T x‖ at h
    rw [T.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg (T x)))
  have h1 := mul_le_mul_of_nonneg_left hx hc.le
  have h2 := mul_le_mul_of_nonneg_left ((helower (T x)).trans hsup) hM.le
  rw [div_mul_eq_mul_div,div_le_iff₀ hKM]
  nlinarith

theorem not_complexDesiredProperty_of_equiv (T : E ≃L[ℂ] F) (hF : ¬ ComplexDesiredProperty F) :
    ¬ ComplexDesiredProperty E := by
  obtain ⟨e,he,hmod⟩ := (not_complexDesiredProperty_iff (E := F)).mp hF
  apply (not_complexDesiredProperty_iff (E := E)).mpr
  refine ⟨complexTransportedNorming T e,complexTransportedNorming_isNorming T he,?_⟩
  intro f
  obtain ⟨g,hg⟩ := hmod (T f)
  refine ⟨T.symm g,fun n => ?_⟩
  rw [complexTransportedNorming_apply,complexTransportedNorming_apply,T.apply_symm_apply,hg n,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (max 1 ‖T.toContinuousLinearMap‖)⁻¹ from
      inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _))),Complex.ofReal_mul]

theorem complexDesiredProperty_equiv (T : E ≃L[ℂ] F) :
    ComplexDesiredProperty E ↔ ComplexDesiredProperty F := by
  constructor
  · intro hE
    by_contra hF
    exact not_complexDesiredProperty_of_equiv T hF hE
  · intro hF
    by_contra hE
    exact not_complexDesiredProperty_of_equiv T.symm hE hF

end SigmaNonprimarity
