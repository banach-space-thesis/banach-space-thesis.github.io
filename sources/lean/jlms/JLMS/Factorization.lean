import JLMS.Adjoint
import JLMS.MainStatements
import JLMS.CZeroIdentity

/-!
# Section 7: factorization bounds and the supremum argument

The general upper bound uses essential norm one for the identity on the dual
of the factor space. That input is now discharged for actual c₀ factorizations
by CZeroIdentity.lean.

`factorizationValues_isLUB_of_sharp` formalizes the concluding argument of
Theorem 1.7. The sharp factorization construction is an explicit hypothesis,
not an axiom, and is still to be proved by Sections 4–7 of the paper.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- UTV = I implies the dual-essential-norm bound in Theorem 1.7.
The general factor space Z has its identity input explicit. The c₀ specialization
below supplies this input from the proved identity lemma. -/
theorem one_le_dual_factorization_product (T : E →L[𝕜] F)
    (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z)
    (hId : essentialNorm (ContinuousLinearMap.id 𝕜 (Z →L[𝕜] 𝕜)) = 1) :
    1 ≤ (‖U‖ * ‖V‖) * dualEssentialNorm T := by
  have hstar : ((banachAdjoint V).comp (banachAdjoint T)).comp (banachAdjoint U) =
      ContinuousLinearMap.id 𝕜 (Z →L[𝕜] 𝕜) := by
    ext φ z
    exact congrArg φ (congrArg (fun A : Z →L[𝕜] Z => A z) hfactor)
  have hbound := essentialNorm_sandwich_le
    (banachAdjoint V) (banachAdjoint T) (banachAdjoint U)
  rw [hstar, hId, norm_banachAdjoint, norm_banachAdjoint] at hbound
  change 1 ≤ ‖V‖ * dualEssentialNorm T * ‖U‖ at hbound
  nlinarith

theorem factorization_norm_product_pos (T : E →L[𝕜] F)
    (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z)
    (hId : essentialNorm (ContinuousLinearMap.id 𝕜 (Z →L[𝕜] 𝕜)) = 1) :
    0 < ‖U‖ * ‖V‖ := by
  have hbound := one_le_dual_factorization_product T U V hfactor hId
  apply lt_of_le_of_ne (mul_nonneg (norm_nonneg U) (norm_nonneg V))
  intro hzero
  rw [← hzero, zero_mul] at hbound
  norm_num at hbound

theorem dual_factorization_bound (T : E →L[𝕜] F)
    (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 Z)
    (hId : essentialNorm (ContinuousLinearMap.id 𝕜 (Z →L[𝕜] 𝕜)) = 1) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ dualEssentialNorm T := by
  have hbound := one_le_dual_factorization_product T U V hfactor hId
  have hpos := factorization_norm_product_pos T U V hfactor hId
  rw [← mul_inv, ← one_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [hbound]

/-- The upper bound in Theorem 1.7 for actual c₀ factorizations, with the
identity-essential-norm input now discharged. -/
theorem dual_factorization_bound_cZero (T : E →L[𝕜] F)
    (U : F →L[𝕜] cZero 𝕜) (V : cZero 𝕜 →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ dualEssentialNorm T :=
  dual_factorization_bound T U V hfactor (essentialNorm_cZero_dual_identity 𝕜)

/-- Any c₀ identity factorization forces positive dual essential norm.
This supplies positivity after Theorem 1.6 without a separate Schauder input. -/
theorem dualEssentialNorm_pos_of_cZero_factorization (T : E →L[𝕜] F)
    (U : F →L[𝕜] cZero 𝕜) (V : cZero 𝕜 →L[𝕜] E)
    (hfactor : (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) :
    0 < dualEssentialNorm T := by
  have hb := one_le_dual_factorization_product T U V hfactor (essentialNorm_cZero_dual_identity 𝕜)
  by_contra h
  have hz : dualEssentialNorm T = 0 :=
    le_antisymm (le_of_not_gt h) (dualEssentialNorm_nonneg T)
  rw [hz, mul_zero] at hb
  norm_num at hb

section CZero

variable {K : Type*} [TopologicalSpace K]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The δ-form of the sharp factorization construction in Section 7.
This definition is a named open proof obligation; it asserts nothing by itself. -/
def SharpFactorizations (T : CZero 𝕜 K →L[𝕜] X) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < dualEssentialNorm T →
    ∃ U : X →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] CZero 𝕜 K,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ * ‖V‖ < 1 / δ

/-- The final supremum step of Theorem 1.7, with its two analytic inputs explicit. -/
theorem factorizationValues_isLUB_of_sharp (T : CZero 𝕜 K →L[𝕜] X)
    (hpositive : 0 < dualEssentialNorm T)
    (hsharp : SharpFactorizations (𝕜 := 𝕜) T)
    (hId : essentialNorm (𝕜 := 𝕜) (E := cZero 𝕜 →L[𝕜] 𝕜) (F := cZero 𝕜 →L[𝕜] 𝕜)
      (ContinuousLinearMap.id 𝕜 (cZero 𝕜 →L[𝕜] 𝕜)) = 1) :
    IsLUB (factorizationValues 𝕜 K X T) (dualEssentialNorm T) := by
  constructor
  · rintro r ⟨U, V, hfactor, rfl⟩
    exact dual_factorization_bound T U V hfactor hId
  · intro b hb
    by_contra h
    have hbd : b < dualEssentialNorm T := lt_of_not_ge h
    let δ := (max b 0 + dualEssentialNorm T) / 2
    have hmax : max b 0 < dualEssentialNorm T := max_lt hbd hpositive
    have hδ : 0 < δ := by dsimp [δ]; linarith [le_max_right b 0]
    have hδd : δ < dualEssentialNorm T := by dsimp [δ]; linarith
    have hbδ : b < δ := by dsimp [δ]; linarith [le_max_left b 0]
    obtain ⟨U, V, hfactor, hnorm⟩ := hsharp δ hδ hδd
    have hpos := factorization_norm_product_pos T U V hfactor hId
    have hrecip : δ < ‖U‖⁻¹ * ‖V‖⁻¹ := by
      have h := one_div_lt_one_div_of_lt hpos hnorm
      simpa [one_div, mul_inv, mul_comm] using h
    have hupper := hb (show ‖U‖⁻¹ * ‖V‖⁻¹ ∈ factorizationValues 𝕜 K X T from
      ⟨U, V, hfactor, rfl⟩)
    linarith

/-- The concluding supremum argument only needs positivity and the sharp
factorization construction; the identity lemma is proved independently. -/
theorem factorizationValues_isLUB_of_sharp_cZero (T : CZero 𝕜 K →L[𝕜] X)
    (hpositive : 0 < dualEssentialNorm T) (hsharp : SharpFactorizations (𝕜 := 𝕜) T) :
    IsLUB (factorizationValues 𝕜 K X T) (dualEssentialNorm T) :=
  factorizationValues_isLUB_of_sharp T hpositive hsharp (essentialNorm_cZero_dual_identity 𝕜)

end CZero

end JLMS
