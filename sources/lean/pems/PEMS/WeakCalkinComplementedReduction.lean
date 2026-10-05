import PEMS.WeakCalkinAutomaticUpperBound

/-! Automatic boundedness survives a weakly compact complemented remainder.
The complement is exhibited by actual bounded maps, and quotient equality
is proved from the genuine weakly compact operator ideal. -/
noncomputable section
open ThesisCommon Set
namespace PEMS
variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem weakCalkinAlgebraNorm_upperBound_of_representative_bound
    (m : WeakCalkin 𝕜 E → ℝ)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ T : E →L[𝕜] E, m (weakCalkinMk 𝕜 E T) ≤ C * ‖T‖) :
    ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  intro x
  refine Submodule.Quotient.induction_on _ x fun T => ?_
  change m (weakCalkinMk 𝕜 E T) ≤ C * weakCalkinNorm 𝕜 E (weakCalkinMk 𝕜 E T)
  rw [weakCalkinNorm_mk]
  have hdiv : m (weakCalkinMk 𝕜 E T) / C ≤ weakEssentialNorm T := by
    apply le_csInf
    · exact ⟨‖T - 0‖, 0, weaklyCompact_zero, rfl⟩
    · rintro r ⟨W, hW, rfl⟩
      have hWzero : (weakCalkinMkCLM 𝕜 E) W = 0 :=
        (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mpr hW
      have heq : m (weakCalkinMk 𝕜 E (T-W)) = m (weakCalkinMk 𝕜 E T) := by
        change m ((weakCalkinMkCLM 𝕜 E) (T-W)) = m ((weakCalkinMkCLM 𝕜 E) T)
        rw [map_sub, hWzero, sub_zero]
      apply (div_le_iff₀ hC).mpr
      simpa only [heq, mul_comm] using hbound (T-W)
  simpa only [mul_comm] using (div_le_iff₀ hC).mp hdiv

theorem weakCalkinMk_eq_compressed_of_weaklyCompact_remainder
    (J : F →L[𝕜] E) (P : E →L[𝕜] F)
    (hrem : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - J.comp P))
    (T : E →L[𝕜] E) :
    weakCalkinMk 𝕜 E T = weakCalkinMk 𝕜 E (J.comp ((P.comp (T.comp J)).comp P)) := by
  let Q := J.comp P
  let R := ContinuousLinearMap.id 𝕜 E - Q
  have hR : IsWeaklyCompactOperator R := hrem
  have hw : IsWeaklyCompactOperator (T - J.comp ((P.comp (T.comp J)).comp P)) := by
    have heq : T - J.comp ((P.comp (T.comp J)).comp P) =
        R.comp T + Q.comp (T.comp R) := by
      ext x
      simp only [R, Q, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_sub]
      abel
    rw [heq]
    exact (hR.comp_right T).add ((hR.comp_left T).comp_left Q)
  apply sub_eq_zero.mp
  change (weakCalkinMkCLM 𝕜 E) T -
    (weakCalkinMkCLM 𝕜 E) (J.comp ((P.comp (T.comp J)).comp P)) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mpr hw

/-- Exact self-copies are needed only in a complemented core. An actual
weakly compact remainder, including a finite-dimensional complement, is harmless. -/
theorem exists_weakCalkinAlgebraNorm_upperBound_of_complemented_core [CompleteSpace F]
    (J : F →L[𝕜] E) (P : E →L[𝕜] F)
    (hPJ : P.comp J = ContinuousLinearMap.id 𝕜 F)
    (hrem : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - J.comp P))
    (I Q : ℕ → F →L[𝕜] F)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 F)
    (ho : ∀ n k, n ≠ k → (Q n).comp (I k) = 0)
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  let V : (F →L[𝕜] F) →ₗ[𝕜] (E →L[𝕜] E) :=
    { toFun := fun T => J.comp (T.comp P)
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp }
  let q := (weakCalkinMkCLM 𝕜 E).toLinearMap.comp V
  let α : (F →L[𝕜] F) → ℝ := fun T => m (q T)
  have hz : α 0 = 0 := by simp only [α, map_zero]; exact (hm.2.1 0).mpr rfl
  have hs (a : 𝕜) (T : F →L[𝕜] F) : α (a • T) = ‖a‖ * α T := by
    simp only [α, map_smul]
    exact hm.2.2.2.1 a _
  have hmul (S T : F →L[𝕜] F) : α (S.comp T) ≤ α S * α T := by
    have heq : V (S.comp T) = (V S).comp (V T) := by
      ext x
      change J (S (T (P x))) = J (S (P (J (T (P x)))))
      have h := congrArg (fun A : F →L[𝕜] F => A (T (P x))) hPJ
      change P (J (T (P x))) = T (P x) at h
      rw [h]
    change m (weakCalkinMk 𝕜 E (V (S.comp T))) ≤
      m (weakCalkinMk 𝕜 E (V S)) * m (weakCalkinMk 𝕜 E (V T))
    rw [heq]
    exact hm.2.2.2.2 _ _
  obtain ⟨C, hC, hb⟩ := exists_algebra_seminorm_bound_of_orthogonal_selfCopies
    I Q hd ho α (fun T => hm.1 _) hz hs hmul
  let D := C * (‖P‖ * ‖J‖ + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, weakCalkinAlgebraNorm_upperBound_of_representative_bound m hD ?_⟩
  intro T
  rw [weakCalkinMk_eq_compressed_of_weaklyCompact_remainder J P hrem T]
  change α (P.comp (T.comp J)) ≤ D * ‖T‖
  calc
    _ ≤ C * ‖P.comp (T.comp J)‖ := hb _
    _ ≤ C * (‖P‖ * (‖T‖ * ‖J‖)) := by
      gcongr
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ D * ‖T‖ := by dsimp [D]; nlinarith [norm_nonneg T]

theorem exists_weakCalkinAlgebraNorm_upperBound_of_weaklyCompact_product
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (e : E ≃L[𝕜] F × G)
    (hG : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 G))
    (I Q : ℕ → F →L[𝕜] F)
    (hd : ∀ n, (Q n).comp (I n) = ContinuousLinearMap.id 𝕜 F)
    (ho : ∀ n k, n ≠ k → (Q n).comp (I k) = 0)
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  let J := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 F G)
  let P := (ContinuousLinearMap.fst 𝕜 F G).comp e.toContinuousLinearMap
  let K := e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr 𝕜 F G)
  let R := (ContinuousLinearMap.snd 𝕜 F G).comp e.toContinuousLinearMap
  have hPJ : P.comp J = ContinuousLinearMap.id 𝕜 F := by ext x; simp [P, J]
  have hrem : ContinuousLinearMap.id 𝕜 E - J.comp P = K.comp R := by
    ext x
    apply e.injective
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_sub, J, P, K, R,
      ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
    apply Prod.ext <;> simp
  apply exists_weakCalkinAlgebraNorm_upperBound_of_complemented_core
    J P hPJ _ I Q hd ho m hm
  rw [hrem]
  simpa only [ContinuousLinearMap.comp_id] using (hG.comp_left K).comp_right R

end PEMS
