import JLMS.CalkinRing
import JLMS.OperatorConjugation

/-!
# Changing Banach-space coordinates in the Calkin algebra

Conjugation preserves compact operators and descends to the actual quotient.
Isometric conjugation preserves its essential norm. Minimality consequently
transfers between isometrically isomorphic Banach spaces.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def calkinQuotientHom : (E →L[𝕜] E) →ₙₐ[𝕜] Calkin 𝕜 E where
  __ := (compactOperator (RingHom.id 𝕜) E E).mkQ
  map_zero' := rfl
  map_mul' := calkinMk_mul

def calkinConjugation (e : E ≃L[𝕜] F) : Calkin 𝕜 E →ₙₐ[𝕜] Calkin 𝕜 F where
  __ := (compactOperator (RingHom.id 𝕜) E E).mapQ
    (compactOperator (RingHom.id 𝕜) F F)
    ({ toFun := operatorConjugation e
       map_add' := (operatorConjugation e).map_add
       map_smul' := (operatorConjugation e).map_smul } : (E →L[𝕜] E) →ₗ[𝕜] (F →L[𝕜] F))
    (by
      intro T hT
      exact (hT.comp_clm e.symm.toContinuousLinearMap).clm_comp e.toContinuousLinearMap)
  map_zero' := map_zero _
  map_mul' := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H S =>
      induction y using Submodule.Quotient.induction_on with
      | H T => exact congrArg (calkinMk 𝕜 F) ((operatorConjugation e).map_mul S T)

@[simp] theorem calkinConjugation_mk (e : E ≃L[𝕜] F) (T : E →L[𝕜] E) :
    calkinConjugation e (calkinMk 𝕜 E T) =
      calkinMk 𝕜 F (operatorConjugation e T) := rfl

@[simp] theorem calkinConjugation_inverse (e : E ≃L[𝕜] F) (q : Calkin 𝕜 E) :
    calkinConjugation e.symm (calkinConjugation e q) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H T =>
    change calkinMk 𝕜 E (operatorConjugation e.symm (operatorConjugation e T)) = calkinMk 𝕜 E T
    rw [operatorConjugation_inverse]

theorem essentialNormIsMinimal_of_isometryEquiv (e : E ≃ₗᵢ[𝕜] F)
    (hF : EssentialNormIsMinimal 𝕜 F) : EssentialNormIsMinimal 𝕜 E := by
  intro n hn
  let m : Calkin 𝕜 F → ℝ := fun q => n (calkinConjugation e.toContinuousLinearEquiv.symm q)
  have hm : IsCalkinAlgebraNorm 𝕜 F m := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro q; exact hn.1.1 _
    · intro q
      rw [hn.1.2.1]
      constructor
      · intro h
        have hh := congrArg (calkinConjugation e.toContinuousLinearEquiv) h
        have hi := calkinConjugation_inverse e.toContinuousLinearEquiv.symm q
        simp only [ContinuousLinearEquiv.symm_symm] at hi
        simpa only [hi, map_zero] using hh
      · intro h; simp [h]
    · intro q r
      change n ((calkinConjugation e.toContinuousLinearEquiv.symm) (q + r)) ≤ _
      rw [map_add]
      exact hn.1.2.2.1 _ _
    · intro a q
      change n ((calkinConjugation e.toContinuousLinearEquiv.symm) (a • q)) = _
      rw [map_smul]
      exact hn.1.2.2.2 _ _
    · intro S T
      change n (calkinMk 𝕜 E (operatorConjugation e.toContinuousLinearEquiv.symm (S * T))) ≤ _
      rw [map_mul]
      exact hn.2 _ _
  obtain ⟨c, hc, hbound⟩ := hF m hm
  refine ⟨c, hc, fun T => ?_⟩
  have h := hbound (operatorConjugation e.toContinuousLinearEquiv T)
  simpa only [m, calkinConjugation_mk, operatorConjugation_inverse,
    essentialNorm_operatorConjugation] using h

end JLMS
