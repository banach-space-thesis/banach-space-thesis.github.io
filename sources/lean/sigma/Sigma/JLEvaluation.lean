import Sigma.FunctionalCharge
import ThesisCommon.Analysis.ClosedSpanDual

/-! Compactum evaluations on JL and uniqueness of its continuous functionals
from singleton, family and constant generators. -/
noncomputable section
namespace SigmaNonprimarity
attribute [local instance] bridgeRealSpace bridgeJLGroup bridgeJLSpace jlDualGroup jlDualSpace

theorem jlFunctional_ext {B : Set (Set Point)} (φ ψ : JL B →L[ℝ] ℝ)
    (hp : ∀ p, φ ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩ =
      ψ ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩)
    (hb : ∀ b : B, φ ⟨characteristic b.val,characteristic_mem_JL b.property⟩ =
      ψ ⟨characteristic b.val,characteristic_mem_JL b.property⟩)
    (h1 : φ ⟨characteristic Set.univ,constant_mem_JL B⟩ = ψ ⟨characteristic Set.univ,constant_mem_JL B⟩) :
    φ = ψ := by
  apply ThesisCommon.closedSpan_dual_ext (jlGenerators B) φ ψ
  rintro x ((⟨p,rfl⟩ | ⟨b,hb',rfl⟩) | rfl)
  · exact hp p
  · exact hb ⟨b,hb'⟩
  · exact h1

def jlEvaluation {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : AUCompactum B) : JL B →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ p).comp (jlContinuousEquiv hB hInf).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem jlEvaluation_apply {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : AUCompactum B) (f : JL B) : jlEvaluation hB hInf p f = jlContinuousEquiv hB hInf f p := rfl

theorem jlEvaluation_base {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : Point) (f : JL B) : jlEvaluation hB hInf (↑(Sum.inl p : MrowkaBase B)) f = f.val p := by
  have h := congrArg (fun g : JL B => g.val p) ((jlContinuousEquiv hB hInf).symm_apply_apply f)
  exact h

theorem jlContinuous_singleton {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (p : Point) : jlContinuousEquiv hB hInf ⟨characteristic {p},characteristic_singleton_mem_JL B p⟩ =
      singletonFunction hB p := by
  simpa only [restrict_singletonFunction] using jlContinuousEquiv_restrict hB hInf
    (singletonFunction hB p) (restrictToBase_mem_JL hB _)

theorem jlContinuous_family {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite)
    (b : B) : jlContinuousEquiv hB hInf ⟨characteristic b.val,characteristic_mem_JL b.property⟩ =
      tailFunction hB b := by
  simpa only [restrict_tailFunction] using jlContinuousEquiv_restrict hB hInf
    (tailFunction hB b) (restrictToBase_mem_JL hB _)

theorem jlContinuous_one {B : Set (Set Point)} (hB : AlmostDisjoint B) (hInf : B.Infinite) :
    jlContinuousEquiv hB hInf ⟨characteristic Set.univ,constant_mem_JL B⟩ = 1 := by
  simpa only [map_one,characteristic_univ] using jlContinuousEquiv_restrict hB hInf
    1 (restrictToBase_mem_JL hB _)

end SigmaNonprimarity
