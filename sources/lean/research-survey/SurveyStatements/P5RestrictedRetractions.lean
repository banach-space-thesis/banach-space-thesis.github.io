import SurveyStatements.P5SubmoduleCopies

/-! A contractive retraction pair preserving a submodule restricts to a
contractive retraction pair on that actual submodule, with an isometric
embedding. No complement or projection is assumed. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P5

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_restricted_contractive_retraction (S : Submodule 𝕜 E)
    (A B : E →L[𝕜] E) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : A.comp B = ContinuousLinearMap.id 𝕜 E)
    (hAS : ∀ x ∈ S, A x ∈ S) (hBS : ∀ x ∈ S, B x ∈ S) :
    ∃ Ar Br : S →L[𝕜] S, ‖Ar‖ ≤ 1 ∧ ‖Br‖ ≤ 1 ∧
      Ar.comp Br = ContinuousLinearMap.id 𝕜 S ∧ ∀ x, ‖Br x‖ = ‖x‖ := by
  let Ar := (A.comp S.subtypeL).codRestrict S (fun x => hAS x x.property)
  let Br := (B.comp S.subtypeL).codRestrict S (fun x => hBS x x.property)
  have hAr : ‖Ar‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using A.le_of_opNorm_le hA x.val
  have hBr : ‖Br‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using B.le_of_opNorm_le hB x.val
  have hArBr : Ar.comp Br = ContinuousLinearMap.id 𝕜 S := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun L : E →L[𝕜] E => L x.val) hAB
  refine ⟨Ar, Br, hAr, hBr, hArBr, fun x => ?_⟩
  have hx : Ar (Br x) = x := congrArg (fun L : S →L[𝕜] S => L x) hArBr
  apply le_antisymm
  · simpa only [one_mul] using Br.le_of_opNorm_le hBr x
  · calc
      ‖x‖ = ‖Ar (Br x)‖ := congrArg norm hx.symm
      _ ≤ ‖Br x‖ := by simpa only [one_mul] using Ar.le_of_opNorm_le hAr (Br x)

end SurveyStatements.P5
