import PEMS.WeakCalkinComplementedReduction

/-! Automatic upper bounds from whole-space corner copies. The diagonal
composition is a common operator whose difference from the identity is
weakly compact. No idempotence of that operator is required: the extraction
identities become exact identities only after taking the weak Calkin quotient. -/
noncomputable section
open ThesisCommon Set Filter
open scoped Topology
namespace PEMS
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

theorem exists_weakCalkinAlgebraNorm_upperBound_of_corner_selfCopies
    (J P : ℕ → E →L[𝕜] E) (Q : E →L[𝕜] E)
    (hdiag : ∀ n, (P n).comp (J n) = Q)
    (hoff : ∀ n k, n ≠ k → (P n).comp (J k) = 0)
    (hrem : IsWeaklyCompactOperator (ContinuousLinearMap.id 𝕜 E - Q))
    (m : WeakCalkin 𝕜 E → ℝ) (hm : IsWeakCalkinAlgebraNorm 𝕜 E m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, m x ≤ C * weakCalkinNorm 𝕜 E x := by
  classical
  let α : (E →L[𝕜] E) → ℝ := fun T => m (weakCalkinMk 𝕜 E T)
  have hnonneg (T : E →L[𝕜] E) : 0 ≤ α T := hm.1 _
  have hzero : α 0 = 0 := by
    change m ((weakCalkinMkCLM 𝕜 E) 0) = 0
    rw [map_zero]
    exact (hm.2.1 0).mpr rfl
  have hsmul (a : 𝕜) (T : E →L[𝕜] E) : α (a • T) = ‖a‖ * α T := by
    change m ((weakCalkinMkCLM 𝕜 E) (a • T)) = ‖a‖ * m ((weakCalkinMkCLM 𝕜 E) T)
    rw [map_smul]
    exact hm.2.2.2.1 a _
  have hmul (S T : E →L[𝕜] E) : α (S.comp T) ≤ α S * α T := hm.2.2.2.2 S T
  have hQ : α Q = α (ContinuousLinearMap.id 𝕜 E) := by
    apply congrArg m
    apply Eq.symm
    apply sub_eq_zero.mp
    change (weakCalkinMkCLM 𝕜 E) (ContinuousLinearMap.id 𝕜 E) -
      (weakCalkinMkCLM 𝕜 E) Q = 0
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero (p := weaklyCompactSubmodule 𝕜 E E)).mpr hrem
  have hcompress (T : E →L[𝕜] E) : α (Q.comp (T.comp Q)) = α T := by
    apply congrArg m
    have h := weakCalkinMk_eq_compressed_of_weaklyCompact_remainder
      Q (ContinuousLinearMap.id 𝕜 E) (by simpa only [ContinuousLinearMap.comp_id] using hrem) T
    simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using h.symm
  have hbound : ∃ C : ℝ, 0 < C ∧ ∀ T, α T ≤ C * ‖T‖ := by
    by_cases hId : α (ContinuousLinearMap.id 𝕜 E) = 0
    · refine ⟨1, zero_lt_one, fun T => ?_⟩
      have h := hmul (ContinuousLinearMap.id 𝕜 E) T
      rw [ContinuousLinearMap.id_comp, hId, zero_mul] at h
      exact h.trans (by simpa only [one_mul] using norm_nonneg T)
    by_contra hbad
    have hIdpos : 0 < α (ContinuousLinearMap.id 𝕜 E) :=
      lt_of_le_of_ne (hnonneg _) (Ne.symm hId)
    have hprod (n : ℕ) : 0 < α (P n) * α (J n) := by
      have h := hmul (P n) (J n)
      rw [hdiag, hQ] at h
      exact hIdpos.trans_le h
    have hex (n : ℕ) : ∃ T : E →L[𝕜] E,
        ‖T‖ ≤ (1 / 2 : ℝ) ^ n / (‖J n‖ * ‖P n‖ + 1) ∧
        ((n : ℝ) + 1) * (α (P n) * α (J n)) < α T :=
      exists_small_norm_large_value_of_unbounded α hzero hsmul hbad (by positivity)
        (mul_nonneg (by positivity) (hprod n).le)
    choose R hRnorm hRlarge using hex
    let F : ℕ → E →L[𝕜] E := fun n => (J n).comp ((R n).comp (P n))
    have hFnorm (n : ℕ) : ‖F n‖ ≤ (1 / 2 : ℝ) ^ n := by
      calc
        _ ≤ ‖J n‖ * (‖R n‖ * ‖P n‖) :=
          ((J n).opNorm_comp_le _).trans
            (mul_le_mul_of_nonneg_left ((R n).opNorm_comp_le _) (norm_nonneg _))
        _ ≤ ‖J n‖ * (((1 / 2 : ℝ) ^ n / (‖J n‖ * ‖P n‖ + 1)) * ‖P n‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hRnorm n) (norm_nonneg _))
            (norm_nonneg _)
        _ ≤ (1 / 2 : ℝ) ^ n := by
          have hd : 0 < ‖J n‖ * ‖P n‖ + 1 := by positivity
          apply (le_of_mul_le_mul_right ?_ hd)
          field_simp
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
    have hs : Summable F := (Summable.of_nonneg_of_le
      (fun n => norm_nonneg (F n)) hFnorm summable_geometric_two).of_norm
    let S : E →L[𝕜] E := ∑' n, F n
    have hterm (n k : ℕ) :
        (P n) * F k * (J n) = if k = n then Q.comp ((R n).comp Q) else 0 := by
      by_cases hkn : k = n
      · subst k
        rw [if_pos rfl]
        change (P n).comp (((J n).comp ((R n).comp (P n))).comp (J n)) = _
        calc
          _ = ((P n).comp (J n)).comp ((R n).comp ((P n).comp (J n))) := by
            simp only [ContinuousLinearMap.comp_assoc]
          _ = _ := by rw [hdiag]
      · rw [if_neg hkn]
        change ((P n).comp ((J k).comp ((R k).comp (P k)))).comp (J n) = 0
        rw [← ContinuousLinearMap.comp_assoc, hoff n k (Ne.symm hkn)]
        simp
    have hcoord (n : ℕ) : (P n) * S * (J n) = Q.comp ((R n).comp Q) := by
      have hsum := (hs.hasSum.mul_left (P n)).mul_right (J n)
      calc
        _ = ∑' k, (P n) * F k * (J n) := hsum.tsum_eq.symm
        _ = Q.comp ((R n).comp Q) := by simp only [hterm]; simp
    have hlarge (n : ℕ) : (n : ℝ) + 1 < α S := by
      have hbound : α (R n) ≤ (α (P n) * α (J n)) * α S := by
        rw [← hcompress (R n), ← hcoord]
        change α (((P n).comp S).comp (J n)) ≤ _
        calc
          _ ≤ α ((P n).comp S) * α (J n) := hmul _ _
          _ ≤ (α (P n) * α S) * α (J n) :=
            mul_le_mul_of_nonneg_right (hmul _ _) (hnonneg _)
          _ = _ := by ring
      exact (mul_lt_mul_iff_right₀ (hprod n)).mp (by
        simpa only [mul_comm] using (hRlarge n).trans_le hbound)
    obtain ⟨n, hn⟩ := exists_nat_gt (α S)
    have h := hlarge n
    linarith
  obtain ⟨C, hC, hCb⟩ := hbound
  exact ⟨C, hC, weakCalkinAlgebraNorm_upperBound_of_representative_bound m hC hCb⟩

end PEMS
