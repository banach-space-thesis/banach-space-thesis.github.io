import PEMS.BonsallFromFactorization

/-! Quantitative comparison of actual quotient algebra norms. The upper
bound is explicit here; the separate automatic-continuity argument is
responsible for constructing it. Sharp ℓ¹ factorization supplies the lower
bound, including when the weak Calkin quotient is zero. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem product_constants_le_scaled_algebraNorm
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x)
    (T : E →L[𝕜] E) (U : E →L[𝕜] EllOne 𝕜) (V : EllOne 𝕜 →L[𝕜] E)
    (hT : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (EllOne 𝕜))
    (P : E →L[𝕜] EllOne 𝕜) (J : EllOne 𝕜 →L[𝕜] E)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 (EllOne 𝕜)) :
    (‖U‖⁻¹ * ‖V‖⁻¹) * (‖P‖⁻¹ * ‖J‖⁻¹) ≤ C ^ 2 * m (weakCalkinMk 𝕜 E T) := by
  have hQ : (J.comp P).comp (J.comp P) = J.comp P := by
    calc
      _ = J.comp ((P.comp J).comp P) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hPJ, ContinuousLinearMap.id_comp]
  have hQW : ¬ IsWeaklyCompactOperator (J.comp P) := by
    intro hw
    have hw' := (hw.comp_right J).comp_left P
    have heq : P.comp ((J.comp P).comp J) = ContinuousLinearMap.id 𝕜 (EllOne 𝕜) := by
      calc
        _ = (P.comp J).comp (P.comp J) := by simp only [ContinuousLinearMap.comp_assoc]
        _ = _ := by rw [hPJ, ContinuousLinearMap.id_comp]
    rw [heq] at hw'
    have hz := hw'.weakEssentialNorm_eq_zero
    rw [weakEssentialNorm_id_scalarEllOne] at hz
    norm_num at hz
  have hOne := one_le_algebraNorm_of_nonweaklyCompact_idempotent m hm (J.comp P) hQ hQW
  have hcomp : (J.comp U).comp (T.comp (V.comp P)) = J.comp P := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg J (DFunLike.congr_fun hT (P x))
  have hnorm (R : E →L[𝕜] E) : m (weakCalkinMk 𝕜 E R) ≤ C * ‖R‖ :=
    (hbound _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [weakCalkinNorm_mk] using weakEssentialNorm_le_norm R) hC.le)
  have hJU : m (weakCalkinMk 𝕜 E (J.comp U)) ≤ C * (‖J‖ * ‖U‖) :=
    (hnorm _).trans (mul_le_mul_of_nonneg_left (J.opNorm_comp_le U) hC.le)
  have hVP : m (weakCalkinMk 𝕜 E (V.comp P)) ≤ C * (‖V‖ * ‖P‖) :=
    (hnorm _).trans (mul_le_mul_of_nonneg_left (V.opNorm_comp_le P) hC.le)
  have hone : 1 ≤ ((‖J‖ * ‖U‖) * (‖V‖ * ‖P‖)) *
      (C ^ 2 * m (weakCalkinMk 𝕜 E T)) := by
    calc
      1 ≤ m (weakCalkinMk 𝕜 E (J.comp P)) := hOne
      _ = m (weakCalkinMk 𝕜 E ((J.comp U).comp (T.comp (V.comp P)))) :=
        congrArg (fun R => m (weakCalkinMk 𝕜 E R)) hcomp.symm
      _ ≤ m (weakCalkinMk 𝕜 E (J.comp U)) *
          m (weakCalkinMk 𝕜 E (T.comp (V.comp P))) := hm.2.2.2.2 _ _
      _ ≤ m (weakCalkinMk 𝕜 E (J.comp U)) *
          (m (weakCalkinMk 𝕜 E T) * m (weakCalkinMk 𝕜 E (V.comp P))) :=
        mul_le_mul_of_nonneg_left (hm.2.2.2.2 _ _) (hm.1 _)
      _ ≤ (C * (‖J‖ * ‖U‖)) * (m (weakCalkinMk 𝕜 E T) * (C * (‖V‖ * ‖P‖))) :=
        mul_le_mul hJU (mul_le_mul_of_nonneg_left hVP (hm.1 _))
          (mul_nonneg (hm.1 _) (hm.1 _)) (by positivity)
      _ = _ := by ring
  have hprod : 0 < (‖J‖ * ‖U‖) * (‖V‖ * ‖P‖) := by
    have hn : 0 ≤ (‖J‖ * ‖U‖) * (‖V‖ * ‖P‖) := by positivity
    by_contra hp
    have hz := le_antisymm (not_lt.mp hp) hn
    rw [hz, zero_mul] at hone
    norm_num at hone
  have hfinal := (inv_le_iff_one_le_mul₀' hprod).mpr hone
  simpa only [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- A quotient algebra norm bounded above by `C` times the canonical norm
is bounded below by `C⁻²` times that norm, under sharp ℓ¹ factorization. -/
theorem weakCalkinNorm_le_sq_mul_of_factorization_and_bound
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup (EllOne 𝕜) T)
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x)
    (x : WeakCalkin 𝕜 E) : weakCalkinNorm 𝕜 E x ≤ C ^ 2 * m x := by
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T) ≤ C ^ 2 * m (weakCalkinMk 𝕜 E T)
  rw [weakCalkinNorm_mk]
  by_cases hId : weakEssentialNorm (ContinuousLinearMap.id 𝕜 E) = 0
  · have hT := weakEssentialNorm_comp_left_le T (ContinuousLinearMap.id 𝕜 E)
    rw [ContinuousLinearMap.comp_id, hId, mul_zero] at hT
    exact hT.trans (mul_nonneg (sq_nonneg _) (hm.1 _))
  have hIdOne := weakEssentialNorm_id_eq_one_of_ne_zero hId
  rw [hfactor T]
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, hUV, rfl⟩)
  · exact mul_nonneg (sq_nonneg _) (hm.1 _)
  · have hr : 0 ≤ ‖U‖⁻¹ * ‖V‖⁻¹ := by positivity
    rcases eq_or_lt_of_le hr with hz | hr
    · rw [← hz]
      exact mul_nonneg (sq_nonneg _) (hm.1 _)
    have hb : factorizationSup (EllOne 𝕜) (ContinuousLinearMap.id 𝕜 E) ≤
        (C ^ 2 * m (weakCalkinMk 𝕜 E T)) / (‖U‖⁻¹ * ‖V‖⁻¹) := by
      apply csSup_le (Set.insert_nonempty _ _)
      rintro r (rfl | ⟨P, J, hPJ, rfl⟩)
      · exact div_nonneg (mul_nonneg (sq_nonneg _) (hm.1 _)) hr.le
      · have hPJ' : P.comp J = ContinuousLinearMap.id 𝕜 (EllOne 𝕜) := by
          simpa only [ContinuousLinearMap.id_comp] using hPJ
        apply (le_div_iff₀ hr).mpr
        simpa only [mul_comm] using
          product_constants_le_scaled_algebraNorm m hm hC hbound T U V hUV P J hPJ'
    rw [← hfactor, hIdOne] at hb
    simpa only [one_mul] using (le_div_iff₀ hr).mp hb

theorem uniqueWeakCalkinAlgebraNorm_of_factorization_and_upperBounds [CompleteSpace E]
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup (EllOne 𝕜) T)
    (hupper : ∀ m : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E m →
      ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x) :
    HasUniqueWeakCalkinAlgebraNorm 𝕜 E := by
  refine ⟨weakCalkinNorm 𝕜 E, weakCalkinNorm_isAlgebraNorm, ?_⟩
  intro m hm
  obtain ⟨C, hC, hb⟩ := hupper m hm
  refine ⟨(C ^ 2)⁻¹, C, inv_pos.mpr (sq_pos_of_pos hC), hC, fun x => ⟨?_, hb x⟩⟩
  have hl := weakCalkinNorm_le_sq_mul_of_factorization_and_bound hfactor m hm hC hb x
  have hdiv : weakCalkinNorm 𝕜 E x / C ^ 2 ≤ m x :=
    (div_le_iff₀ (sq_pos_of_pos hC)).mpr (by simpa only [mul_comm] using hl)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem minimalWeakCalkinNorm_of_factorization_and_upperBounds [CompleteSpace E]
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup (EllOne 𝕜) T)
    (hupper : ∀ m : WeakCalkin 𝕜 E → ℝ, IsWeakCalkinAlgebraNorm 𝕜 E m →
      ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x) :
    IsMinimalWeakCalkinNorm 𝕜 E weakEssentialNorm := by
  refine ⟨weakCalkinNorm 𝕜 E, weakCalkinNorm_isAlgebraNorm, weakCalkinNorm_mk, ?_⟩
  intro m hm
  obtain ⟨C, hC, hb⟩ := hupper m hm
  refine ⟨(C ^ 2)⁻¹, inv_pos.mpr (sq_pos_of_pos hC), fun x => ?_⟩
  have hl := weakCalkinNorm_le_sq_mul_of_factorization_and_bound hfactor m hm hC hb x
  have hdiv : weakCalkinNorm 𝕜 E x / C ^ 2 ≤ m x :=
    (div_le_iff₀ (sq_pos_of_pos hC)).mpr (by simpa only [mul_comm] using hl)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

end PEMS
