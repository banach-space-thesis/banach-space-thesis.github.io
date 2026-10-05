import JLMS.Adjoint

/-!
# Section 8: the Bonsall minimality argument

The final proof is abstracted over a factor space Z. Its inputs are the
noncompact contractive retract of Lemma 8.1 and arbitrarily good factorizations
of the identity. Those inputs are hypotheses, not asserted paper results.
This abstraction makes the concluding argument reusable for other spaces.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A nonzero idempotent has norm at least one in every algebra norm. -/
theorem one_le_calkinNorm_of_idempotent (n : Calkin 𝕜 E → ℝ)
    (hn : IsCalkinAlgebraNorm 𝕜 E n) (P : E →L[𝕜] E)
    (hP : P.comp P = P) (hcompact : ¬ IsCompactOperator P) :
    1 ≤ n (calkinMk 𝕜 E P) := by
  have hpos : 0 < n (calkinMk 𝕜 E P) := by
    apply lt_of_le_of_ne (hn.1.1 _)
    intro hzero
    have hclass := (hn.1.2.1 _).mp hzero.symm
    exact hcompact ((Submodule.Quotient.mk_eq_zero _).mp hclass)
  have hsub := hn.2 P P
  rw [hP] at hsub
  nlinarith

/-- The paper's idempotent estimate before taking ε to zero. -/
theorem bonsall_factorization_estimate
    (n : Calkin 𝕜 E → ℝ) (hn : IsCalkinAlgebraNorm 𝕜 E n)
    (hdom : ∀ S : E →L[𝕜] E, n (calkinMk 𝕜 E S) ≤ dualEssentialNorm S)
    (A : Z →L[𝕜] E) (B : E →L[𝕜] Z)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 Z)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hP : ¬ IsCompactOperator (A.comp B))
    (T : E →L[𝕜] E) (U : E →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z) :
    1 ≤ (‖U‖ * ‖V‖) * n (calkinMk 𝕜 E T) := by
  have hidempotent : (A.comp B).comp (A.comp B) = A.comp B := by
    ext x
    have hx := congrArg (fun S : Z →L[𝕜] Z => A (S (B x))) hBA
    exact hx
  have hone := one_le_calkinNorm_of_idempotent n hn (A.comp B) hidempotent hP
  have hrewrite : ((A.comp U).comp T).comp (V.comp B) = A.comp B := by
    ext x
    exact congrArg (fun S : Z →L[𝕜] Z => A (S (B x))) hfactor
  have hsub₁ := hn.2 ((A.comp U).comp T) (V.comp B)
  have hsub₂ := hn.2 (A.comp U) T
  have hAU : n (calkinMk 𝕜 E (A.comp U)) ≤ ‖U‖ := calc
    _ ≤ dualEssentialNorm (A.comp U) := hdom _
    _ ≤ ‖A.comp U‖ := dualEssentialNorm_le_norm _
    _ ≤ ‖A‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le A U
    _ ≤ ‖U‖ := by simpa using mul_le_mul_of_nonneg_right hA (norm_nonneg U)
  have hVB : n (calkinMk 𝕜 E (V.comp B)) ≤ ‖V‖ := calc
    _ ≤ dualEssentialNorm (V.comp B) := hdom _
    _ ≤ ‖V.comp B‖ := dualEssentialNorm_le_norm _
    _ ≤ ‖V‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le V B
    _ ≤ ‖V‖ := by simpa using mul_le_mul_of_nonneg_left hB (norm_nonneg V)
  rw [hrewrite] at hsub₁
  have hnT := hn.1.1 (calkinMk 𝕜 E T)
  have hnVB := hn.1.1 (calkinMk 𝕜 E (V.comp B))
  calc
    1 ≤ n (calkinMk 𝕜 E (A.comp B)) := hone
    _ ≤ n (calkinMk 𝕜 E ((A.comp U).comp T)) *
        n (calkinMk 𝕜 E (V.comp B)) := hsub₁
    _ ≤ (n (calkinMk 𝕜 E (A.comp U)) * n (calkinMk 𝕜 E T)) *
        n (calkinMk 𝕜 E (V.comp B)) := mul_le_mul_of_nonneg_right hsub₂ hnVB
    _ ≤ (‖U‖ * n (calkinMk 𝕜 E T)) * ‖V‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_right hAU hnT) hVB hnVB
        (mul_nonneg (norm_nonneg U) hnT)
    _ = (‖U‖ * ‖V‖) * n (calkinMk 𝕜 E T) := by ring

/-- The concluding argument of Theorem 1.5, with the retract and sharp
factorizations still explicit. The d = 0 case does not require a factorization. -/
theorem bonsall_minimality_of_factorizations
    (A : Z →L[𝕜] E) (B : E →L[𝕜] Z)
    (hBA : B.comp A = ContinuousLinearMap.id 𝕜 Z)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hP : ¬ IsCompactOperator (A.comp B))
    (hsharp : ∀ T : E →L[𝕜] E, 0 < dualEssentialNorm T →
      ∀ ε : ℝ, 0 < ε → ∃ U : E →L[𝕜] Z, ∃ V : Z →L[𝕜] E,
        (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z ∧
        ‖U‖ * ‖V‖ < 1 / dualEssentialNorm T + ε) :
    DualEssentialNormHasBonsallMinimality 𝕜 E := by
  intro n hn hdom T
  apply le_antisymm (hdom T)
  by_cases hzero : dualEssentialNorm T = 0
  · rw [hzero]
    exact hn.1.1 _
  have hd : 0 < dualEssentialNorm T :=
    lt_of_le_of_ne (dualEssentialNorm_nonneg T) (Ne.symm hzero)
  have hlimit : 1 ≤ (1 / dualEssentialNorm T) * n (calkinMk 𝕜 E T) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hnT := hn.1.1 (calkinMk 𝕜 E T)
    have hden : 0 < n (calkinMk 𝕜 E T) + 1 := by linarith
    obtain ⟨U, V, hfactor, hnorm⟩ := hsharp T hd (ε / (n (calkinMk 𝕜 E T) + 1))
      (div_pos hε hden)
    have hest := bonsall_factorization_estimate n hn hdom A B hBA hA hB hP T U V hfactor
    have hmul := mul_le_mul_of_nonneg_right hnorm.le hnT
    have hdiv := div_mul_cancel₀ ε (ne_of_gt hden)
    have hsmall : 0 ≤ ε / (n (calkinMk 𝕜 E T) + 1) := le_of_lt (div_pos hε hden)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlimit hd.le
  have hcancel : dualEssentialNorm T * (1 / dualEssentialNorm T) = 1 :=
    mul_one_div_cancel (ne_of_gt hd)
  nlinarith

end JLMS
