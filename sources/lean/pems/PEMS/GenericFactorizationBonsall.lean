import PEMS.BonsallFromFactorization
import ThesisCommon.Analysis.DualWeakCalkinNorm

/-! Bonsall minimality from a sharp factorization formula through any space
whose identity is not weakly compact. Competing norms may be incomplete. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 E Z : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
theorem generic_product_factorization_constants_le_algebraNorm
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m)
    (hdom : ∀ R : E →L[𝕜] E, m (weakCalkinMk 𝕜 E R) ≤ ‖R‖)
    (T : E →L[𝕜] E) (U : E →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hT : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z)
    (P : E →L[𝕜] Z) (J : Z →L[𝕜] E)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Z) :
    (‖U‖⁻¹ * ‖V‖⁻¹) * (‖P‖⁻¹ * ‖J‖⁻¹) ≤ m (weakCalkinMk 𝕜 E T) := by
  have hQ : (J.comp P).comp (J.comp P) = J.comp P := by
    calc
      _ = J.comp ((P.comp J).comp P) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hPJ, ContinuousLinearMap.id_comp]
  have hQW : ¬ IsWeaklyCompactOperator (J.comp P) := by
    intro hw
    have hw' := (hw.comp_right J).comp_left P
    have heq : P.comp ((J.comp P).comp J) = ContinuousLinearMap.id 𝕜 Z := by
      calc
        _ = (P.comp J).comp (P.comp J) := by simp only [ContinuousLinearMap.comp_assoc]
        _ = _ := by rw [hPJ, ContinuousLinearMap.id_comp]
    rw [heq] at hw'
    exact hZ hw'
  have hOne := one_le_algebraNorm_of_nonweaklyCompact_idempotent m hm (J.comp P) hQ hQW
  have hcomp : (J.comp U).comp (T.comp (V.comp P)) = J.comp P := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg J (DFunLike.congr_fun hT (P x))
  have hJU : m (weakCalkinMk 𝕜 E (J.comp U)) ≤ ‖J‖ * ‖U‖ :=
    (hdom _).trans (J.opNorm_comp_le U)
  have hVP : m (weakCalkinMk 𝕜 E (V.comp P)) ≤ ‖V‖ * ‖P‖ :=
    (hdom _).trans (V.opNorm_comp_le P)
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


theorem generic_quotientNorm_id_eq_one_of_ne_zero
    (n : WeakCalkin 𝕜 E → ℝ) (hn : IsWeakCalkinAlgebraNorm 𝕜 E n)
    (hbound : ∀ T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E T) ≤ ‖T‖)
    (hId : n (weakCalkinMk 𝕜 E (ContinuousLinearMap.id 𝕜 E)) ≠ 0) :
    n (weakCalkinMk 𝕜 E (ContinuousLinearMap.id 𝕜 E)) = 1 := by
  have hp := lt_of_le_of_ne (hn.1 (weakCalkinMk 𝕜 E (ContinuousLinearMap.id 𝕜 E)))
    (Ne.symm hId)
  have hb := (hbound (ContinuousLinearMap.id 𝕜 E)).trans ContinuousLinearMap.norm_id_le
  have hm := hn.2.2.2.2 (ContinuousLinearMap.id 𝕜 E) (ContinuousLinearMap.id 𝕜 E)
  simp only [ContinuousLinearMap.id_comp] at hm
  nlinarith

theorem bonsallWeakCalkinMinimality_of_generic_factorization
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (n : WeakCalkin 𝕜 E → ℝ) (hn : IsWeakCalkinAlgebraNorm 𝕜 E n)
    (hbound : ∀ T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E T) ≤ ‖T‖)
    (hfactor : ∀ T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E T) = factorizationSup Z T) :
    HasBonsallWeakCalkinMinimality 𝕜 E (fun T => n (weakCalkinMk 𝕜 E T)) := by
  refine ⟨n, hn, fun _ => rfl, ?_⟩
  intro m hm hdom
  funext x
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change m (weakCalkinMk 𝕜 E T) = n (weakCalkinMk 𝕜 E T)
  apply le_antisymm (hdom _)
  by_cases hId : n (weakCalkinMk 𝕜 E (ContinuousLinearMap.id 𝕜 E)) = 0
  · have hT := hn.2.2.2.2 (ContinuousLinearMap.id 𝕜 E) T
    rw [ContinuousLinearMap.id_comp, hId, zero_mul] at hT
    exact hT.trans (hm.1 _)
  have hIdOne := generic_quotientNorm_id_eq_one_of_ne_zero n hn hbound hId
  rw [hfactor T]
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, hUV, rfl⟩)
  · exact hm.1 _
  · have hr : 0 ≤ ‖U‖⁻¹ * ‖V‖⁻¹ := by positivity
    rcases eq_or_lt_of_le hr with hz | hr
    · rw [← hz]
      exact hm.1 _
    have hb : factorizationSup Z (ContinuousLinearMap.id 𝕜 E) ≤
        m (weakCalkinMk 𝕜 E T) / (‖U‖⁻¹ * ‖V‖⁻¹) := by
      apply csSup_le (Set.insert_nonempty _ _)
      rintro r (rfl | ⟨P, J, hPJ, rfl⟩)
      · exact div_nonneg (hm.1 _) hr.le
      · have hPJ' : P.comp J = ContinuousLinearMap.id 𝕜 Z := by
          simpa only [ContinuousLinearMap.id_comp] using hPJ
        apply (le_div_iff₀ hr).mpr
        simpa only [mul_comm] using generic_product_factorization_constants_le_algebraNorm
          hZ m hm (fun R => (hdom _).trans (hbound R)) T U V hUV P J hPJ'
    rw [← hfactor, hIdOne] at hb
    simpa only [one_mul] using (le_div_iff₀ hr).mp hb

theorem bonsall_weakEssentialNorm_of_generic_factorization [CompleteSpace E]
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (hfactor : ∀ T : E →L[𝕜] E, weakEssentialNorm T = factorizationSup Z T) :
    HasBonsallWeakCalkinMinimality 𝕜 E weakEssentialNorm := by
  have h := bonsallWeakCalkinMinimality_of_generic_factorization hZ
    (weakCalkinNorm 𝕜 E) weakCalkinNorm_isAlgebraNorm
    (fun T => by simpa only [weakCalkinNorm_mk] using weakEssentialNorm_le_norm T)
    (fun T => by simpa only [weakCalkinNorm_mk] using hfactor T)
  simpa only [weakCalkinNorm_mk] using h

theorem bonsall_dualWeakEssentialNorm_of_generic_factorization [CompleteSpace E]
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (hfactor : ∀ T : E →L[𝕜] E, dualWeakEssentialNorm T = factorizationSup Z T) :
    HasBonsallWeakCalkinMinimality 𝕜 E dualWeakEssentialNorm := by
  have h := bonsallWeakCalkinMinimality_of_generic_factorization hZ
    (dualWeakCalkinNorm 𝕜 E) dualWeakCalkinNorm_isAlgebraNorm
    (fun T => by
      rw [dualWeakCalkinNorm_mk]
      exact (weakEssentialNorm_banachAdjoint_le T).trans (weakEssentialNorm_le_norm T))
    (fun T => by simpa only [dualWeakCalkinNorm_mk, dualWeakEssentialNorm] using hfactor T)
  simpa only [dualWeakCalkinNorm_mk, dualWeakEssentialNorm] using h

end PEMS
