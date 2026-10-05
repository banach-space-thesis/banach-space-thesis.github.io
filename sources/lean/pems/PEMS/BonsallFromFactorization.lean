import PEMS.EllOneFactorizationUpperBound
import ThesisCommon.Analysis.WeakCalkinNorm

/-! A generic conditional Bonsall-minimality assembly. The only outstanding
geometric input is the explicitly stated sharp scalar-ℓ¹ factorization
formula for every endomorphism. Near-extremal factorizations of the identity
supply the complemented copies; none is assumed as additional structure.
This module alone does not assert the AL-space or C(K)-space corollaries. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem one_le_algebraNorm_of_nonweaklyCompact_idempotent
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m)
    (P : E →L[𝕜] E) (hP : P.comp P = P) (hPW : ¬ IsWeaklyCompactOperator P) :
    1 ≤ m (weakCalkinMk 𝕜 E P) := by
  have hne : weakCalkinMk 𝕜 E P ≠ 0 := by
    intro h
    apply hPW
    exact (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mp h
  have hp : 0 < m (weakCalkinMk 𝕜 E P) :=
    lt_of_le_of_ne (hm.1 _) (Ne.symm fun h => hne ((hm.2.1 _).mp h))
  have hmul := hm.2.2.2.2 P P
  rw [hP] at hmul
  nlinarith

theorem weakEssentialNorm_id_eq_one_of_ne_zero
    (h : weakEssentialNorm (ContinuousLinearMap.id 𝕜 E) ≠ 0) :
    weakEssentialNorm (ContinuousLinearMap.id 𝕜 E) = 1 := by
  have hnonneg := weakEssentialNorm_nonneg (ContinuousLinearMap.id 𝕜 E)
  have hpos := lt_of_le_of_ne hnonneg (Ne.symm h)
  have hle := (weakEssentialNorm_le_norm (ContinuousLinearMap.id 𝕜 E)).trans
    ContinuousLinearMap.norm_id_le
  have hmul := weakEssentialNorm_comp_le (ContinuousLinearMap.id 𝕜 E)
    (ContinuousLinearMap.id 𝕜 E)
  simpa using (show weakEssentialNorm (ContinuousLinearMap.id 𝕜 E) = 1 from by
    simp only [ContinuousLinearMap.id_comp] at hmul
    nlinarith)

private theorem product_factorization_constants_le_dominated_algebraNorm
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m)
    (hdom : ∀ x, m x ≤ weakCalkinNorm 𝕜 E x)
    (T : E →L[𝕜] E) (U : E →L[𝕜] EllOne 𝕜) (V : EllOne 𝕜 →L[𝕜] E)
    (hT : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 (EllOne 𝕜))
    (P : E →L[𝕜] EllOne 𝕜) (J : EllOne 𝕜 →L[𝕜] E)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 (EllOne 𝕜)) :
    (‖U‖⁻¹ * ‖V‖⁻¹) * (‖P‖⁻¹ * ‖J‖⁻¹) ≤ m (weakCalkinMk 𝕜 E T) := by
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
  have hJU : m (weakCalkinMk 𝕜 E (J.comp U)) ≤ ‖J‖ * ‖U‖ :=
    ((hdom _).trans (by simpa only [weakCalkinNorm_mk] using
      weakEssentialNorm_le_norm (J.comp U))).trans (J.opNorm_comp_le U)
  have hVP : m (weakCalkinMk 𝕜 E (V.comp P)) ≤ ‖V‖ * ‖P‖ :=
    ((hdom _).trans (by simpa only [weakCalkinNorm_mk] using
      weakEssentialNorm_le_norm (V.comp P))).trans (V.opNorm_comp_le P)
  have hone : 1 ≤ ((‖J‖ * ‖U‖) * (‖V‖ * ‖P‖)) * m (weakCalkinMk 𝕜 E T) := by
    calc
      1 ≤ m (weakCalkinMk 𝕜 E (J.comp P)) := hOne
      _ = m (weakCalkinMk 𝕜 E ((J.comp U).comp (T.comp (V.comp P)))) :=
        congrArg (fun R => m (weakCalkinMk 𝕜 E R)) hcomp.symm
      _ ≤ m (weakCalkinMk 𝕜 E (J.comp U)) *
          m (weakCalkinMk 𝕜 E (T.comp (V.comp P))) := hm.2.2.2.2 _ _
      _ ≤ m (weakCalkinMk 𝕜 E (J.comp U)) *
          (m (weakCalkinMk 𝕜 E T) * m (weakCalkinMk 𝕜 E (V.comp P))) :=
        mul_le_mul_of_nonneg_left (hm.2.2.2.2 _ _) (hm.1 _)
      _ ≤ (‖J‖ * ‖U‖) * (m (weakCalkinMk 𝕜 E T) * (‖V‖ * ‖P‖)) :=
        mul_le_mul hJU (mul_le_mul_of_nonneg_left hVP (hm.1 _))
          (mul_nonneg (hm.1 _) (hm.1 _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have hprod : 0 < (‖J‖ * ‖U‖) * (‖V‖ * ‖P‖) := by
    have hn : 0 ≤ (‖J‖ * ‖U‖) * (‖V‖ * ‖P‖) := by positivity
    by_contra hp
    have hz := le_antisymm (not_lt.mp hp) hn
    rw [hz, zero_mul] at hone
    norm_num at hone
  have hfinal := (inv_le_iff_one_le_mul₀' hprod).mpr hone
  simpa only [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- Sharp ℓ¹ factorization for every endomorphism implies exact equality
of every quotient algebra norm dominated by the weak essential norm.
Completeness is used only to make the canonical quotient norm definite. -/
theorem bonsallWeakCalkinMinimality_of_ellOne_factorization [CompleteSpace E]
    (hfactor : ∀ T : E →L[𝕜] E,
      weakEssentialNorm T = factorizationSup (EllOne 𝕜) T) :
    HasBonsallWeakCalkinMinimality 𝕜 E weakEssentialNorm := by
  refine ⟨weakCalkinNorm 𝕜 E, weakCalkinNorm_isAlgebraNorm, weakCalkinNorm_mk, ?_⟩
  intro m hm hdom
  funext x
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change m (weakCalkinMk 𝕜 E T) = weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T)
  apply le_antisymm (hdom _)
  rw [weakCalkinNorm_mk]
  by_cases hId : weakEssentialNorm (ContinuousLinearMap.id 𝕜 E) = 0
  · have hT := weakEssentialNorm_comp_left_le T (ContinuousLinearMap.id 𝕜 E)
    rw [ContinuousLinearMap.comp_id, hId, mul_zero] at hT
    exact hT.trans (hm.1 _)
  have hIdOne := weakEssentialNorm_id_eq_one_of_ne_zero hId
  rw [hfactor T]
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, hUV, rfl⟩)
  · exact hm.1 _
  · have hr : 0 ≤ ‖U‖⁻¹ * ‖V‖⁻¹ := by positivity
    rcases eq_or_lt_of_le hr with hz | hr
    · rw [← hz]
      exact hm.1 _
    have hb : factorizationSup (EllOne 𝕜) (ContinuousLinearMap.id 𝕜 E) ≤
        m (weakCalkinMk 𝕜 E T) / (‖U‖⁻¹ * ‖V‖⁻¹) := by
      apply csSup_le (Set.insert_nonempty _ _)
      rintro r (rfl | ⟨P, J, hPJ, rfl⟩)
      · exact div_nonneg (hm.1 _) hr.le
      · have hPJ' : P.comp J = ContinuousLinearMap.id 𝕜 (EllOne 𝕜) := by
          simpa only [ContinuousLinearMap.id_comp] using hPJ
        apply (le_div_iff₀ hr).mpr
        simpa only [mul_comm] using
          product_factorization_constants_le_dominated_algebraNorm m hm hdom T U V hUV P J hPJ'
    rw [← hfactor, hIdOne] at hb
    simpa only [one_mul] using (le_div_iff₀ hr).mp hb

end PEMS
