import SurveyStatements.P4Bidual
import Mathlib.Analysis.Normed.Operator.Prod

/-! Continuous-dual reflexivity is preserved by the actual normed product. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SurveyStatements.P4

universe u v w
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem reflexive_prod (hE : IsReflexiveNormedSpace 𝕜 E)
    (hF : IsReflexiveNormedSpace 𝕜 F) : IsReflexiveNormedSpace 𝕜 (E × F) := by
  intro ξ
  obtain ⟨x, hx⟩ := hE (bidualMap (ContinuousLinearMap.fst 𝕜 E F) ξ)
  obtain ⟨y, hy⟩ := hF (bidualMap (ContinuousLinearMap.snd 𝕜 E F) ξ)
  refine ⟨(x, y), ?_⟩
  apply ContinuousLinearMap.ext
  intro φ
  let φE := φ.comp (ContinuousLinearMap.inl 𝕜 E F)
  let φF := φ.comp (ContinuousLinearMap.inr 𝕜 E F)
  have hφ : φ = φE.comp (ContinuousLinearMap.fst 𝕜 E F) +
      φF.comp (ContinuousLinearMap.snd 𝕜 E F) := by
    apply ContinuousLinearMap.ext
    intro z
    change φ z = φ (z.1, 0) + φ (0, z.2)
    rw [← map_add]
    simp
  have hx' : φE x = ξ (φE.comp (ContinuousLinearMap.fst 𝕜 E F)) :=
    congrArg (fun η => η φE) hx
  have hy' : φF y = ξ (φF.comp (ContinuousLinearMap.snd 𝕜 E F)) :=
    congrArg (fun η => η φF) hy
  change φ (x, y) = ξ φ
  calc
    φ (x, y) = φE x + φF y := by
      change φ (x, y) = φ (x, 0) + φ (0, y)
      rw [← map_add]
      simp
    _ = ξ (φE.comp (ContinuousLinearMap.fst 𝕜 E F)) +
        ξ (φF.comp (ContinuousLinearMap.snd 𝕜 E F)) := by rw [hx', hy']
    _ = ξ φ := by rw [← map_add, ← hφ]

end SurveyStatements.P4
