import PEMS.GenericFactorizationBonsall
import ThesisCommon.Analysis.RectangularAlgebraAutomaticBound

/-! Minimality against all algebra norms follows from a sharp factorization
formula and actual orthogonal self-copies of the factor space. The automatic
bounds concern rectangular factors only; no maximality premise is used. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 E Z : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem factorizationSup_le_rectangular_bound
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m)
    (J : Z →L[𝕜] E) (P : E →L[𝕜] Z) (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 Z)
    {C D : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hleft : ∀ U : E →L[𝕜] Z, m (weakCalkinMk 𝕜 E (J.comp U)) ≤ C * ‖U‖)
    (hright : ∀ V : Z →L[𝕜] E, m (weakCalkinMk 𝕜 E (V.comp P)) ≤ D * ‖V‖)
    (T : E →L[𝕜] E) : factorizationSup Z T ≤ (C * D) * m (weakCalkinMk 𝕜 E T) := by
  have hQ : (J.comp P).comp (J.comp P) = J.comp P := by
    calc
      _ = J.comp ((P.comp J).comp P) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = _ := by rw [hPJ, ContinuousLinearMap.id_comp]
  have hQW : ¬ IsWeaklyCompactOperator (J.comp P) := by
    intro hw
    apply hZ
    have hw' := (hw.comp_right J).comp_left P
    have heq : P.comp ((J.comp P).comp J) = ContinuousLinearMap.id 𝕜 Z := by
      calc
        _ = (P.comp J).comp (P.comp J) := by simp only [ContinuousLinearMap.comp_assoc]
        _ = _ := by rw [hPJ, ContinuousLinearMap.id_comp]
    rwa [heq] at hw'
  have hOne := one_le_algebraNorm_of_nonweaklyCompact_idempotent m hm (J.comp P) hQ hQW
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, hUV, rfl⟩)
  · exact mul_nonneg (mul_pos hC hD).le (hm.1 _)
  · have hcomp : (J.comp U).comp (T.comp (V.comp P)) = J.comp P := by
      ext x
      exact congrArg J (DFunLike.congr_fun hUV (P x))
    have hone : 1 ≤ (‖U‖ * ‖V‖) * ((C * D) * m (weakCalkinMk 𝕜 E T)) := by
      calc
        1 ≤ m (weakCalkinMk 𝕜 E (J.comp P)) := hOne
        _ = m (weakCalkinMk 𝕜 E ((J.comp U).comp (T.comp (V.comp P)))) :=
          congrArg (fun R => m (weakCalkinMk 𝕜 E R)) hcomp.symm
        _ ≤ m (weakCalkinMk 𝕜 E (J.comp U)) *
            m (weakCalkinMk 𝕜 E (T.comp (V.comp P))) := hm.2.2.2.2 _ _
        _ ≤ m (weakCalkinMk 𝕜 E (J.comp U)) *
            (m (weakCalkinMk 𝕜 E T) * m (weakCalkinMk 𝕜 E (V.comp P))) :=
          mul_le_mul_of_nonneg_left (hm.2.2.2.2 _ _) (hm.1 _)
        _ ≤ (C * ‖U‖) * (m (weakCalkinMk 𝕜 E T) * (D * ‖V‖)) :=
          mul_le_mul (hleft U) (mul_le_mul_of_nonneg_left (hright V) (hm.1 _))
            (mul_nonneg (hm.1 _) (hm.1 _)) (mul_nonneg hC.le (norm_nonneg _))
        _ = _ := by ring
    have hp : 0 < ‖U‖ * ‖V‖ := by
      by_contra hh
      have hz : ‖U‖ * ‖V‖ = 0 := le_antisymm (not_lt.mp hh) (by positivity)
      rw [hz, zero_mul] at hone
      norm_num at hone
    have hh := (inv_le_iff_one_le_mul₀' hp).mpr hone
    simpa only [mul_inv_rev, mul_comm] using hh

theorem minimalWeakCalkinNorm_of_generic_factorization [CompleteSpace E] [CompleteSpace Z]
    (hZ : ¬ IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 Z))
    (I Q : ℕ → Z →L[𝕜] Z)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 Z)
    (ho : ∀ n m, n ≠ m → (Q n).comp (I m) = 0)
    (n : WeakCalkin 𝕜 E → ℝ) (hn : IsWeakCalkinAlgebraNorm 𝕜 E n)
    (hfactor : ∀ T : E →L[𝕜] E, n (weakCalkinMk 𝕜 E T) = factorizationSup Z T) :
    IsMinimalWeakCalkinNorm 𝕜 E (fun T => n (weakCalkinMk 𝕜 E T)) := by
  refine ⟨n, hn, fun _ => rfl, ?_⟩
  intro m hm
  by_cases hId : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E)
  · refine ⟨1, zero_lt_one, fun x => ?_⟩
    have hx : x = 0 := by
      refine Submodule.Quotient.induction_on _ x fun T => ?_
      apply (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mpr
      simpa only [ContinuousLinearMap.comp_id] using hId.comp_left T
    rw [hx, (hn.2.1 0).mpr rfl, (hm.2.1 0).mpr rfl]
    simp
  have hex : ∃ P : E →L[𝕜] Z, ∃ J : Z →L[𝕜] E,
      P.comp J = ContinuousLinearMap.id 𝕜 Z := by
    by_contra hbad
    have hempty : {r : ℝ | ∃ P : E →L[𝕜] Z, ∃ J : Z →L[𝕜] E,
        P.comp ((ContinuousLinearMap.id 𝕜 E).comp J) = ContinuousLinearMap.id 𝕜 Z ∧
        r = ‖P‖⁻¹ * ‖J‖⁻¹} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro r ⟨P, J, hPJ, _⟩
      exact hbad ⟨P, J, by simpa only [ContinuousLinearMap.id_comp] using hPJ⟩
    have hz : n (weakCalkinMk 𝕜 E (ContinuousLinearMap.id 𝕜 E)) = 0 := by
      rw [hfactor, factorizationSup, hempty]
      simp
    exact hId ((Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mp
      ((hn.2.1 _).mp hz))
  obtain ⟨P, J, hPJ⟩ := hex
  let α : (E →L[𝕜] E) → ℝ := fun T => m (weakCalkinMk 𝕜 E T)
  have hz : α 0 = 0 := by
    change m ((weakCalkinMkCLM 𝕜 E) 0) = 0
    rw [map_zero]
    exact (hm.2.1 0).mpr rfl
  have hs (a : 𝕜) (T : E →L[𝕜] E) : α (a • T) = ‖a‖ * α T := by
    change m ((weakCalkinMkCLM 𝕜 E) (a • T)) = ‖a‖ * m ((weakCalkinMkCLM 𝕜 E) T)
    rw [map_smul]
    exact hm.2.2.2.1 a _
  obtain ⟨C, hC, hleft⟩ := exists_left_rectangular_algebra_bound
    J P hPJ I Q hd ho α (fun _ => hm.1 _) hz hs (fun S T => hm.2.2.2.2 S T)
  obtain ⟨D, hD, hright⟩ := exists_right_rectangular_algebra_bound
    J P hPJ I Q hd ho α (fun _ => hm.1 _) hz hs (fun S T => hm.2.2.2.2 S T)
  refine ⟨(C * D)⁻¹, inv_pos.mpr (mul_pos hC hD), fun x => ?_⟩
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change (C * D)⁻¹ * n (weakCalkinMk 𝕜 E T) ≤ m (weakCalkinMk 𝕜 E T)
  rw [hfactor]
  have hb := factorizationSup_le_rectangular_bound hZ m hm J P hPJ hC hD hleft hright T
  have hh : factorizationSup Z T / (C * D) ≤ m (weakCalkinMk 𝕜 E T) :=
    (div_le_iff₀ (mul_pos hC hD)).mpr (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using hh

end PEMS
