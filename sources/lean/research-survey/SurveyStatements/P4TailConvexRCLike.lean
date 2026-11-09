import SurveyStatements.P4TailConvexRadial
import Mathlib.Analysis.Normed.Module.RCLike.Extend

noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped BigOperators

namespace SurveyStatements.P4

variable {𝕜 K E : Type*} [RCLike 𝕜]
  [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Complex (or real) weak pointwise convergence supplies the real weak tests
used in scalarization, by the actual extension of real functionals. -/
theorem weak_pointwise_real_tests
    (fseq : ℕ → C(K, E)) (f : K → E)
    (hweak : ∀ t (φ : StrongDual 𝕜 E),
      Tendsto (fun n => φ (fseq n t)) atTop (𝓝 (φ (f t)))) :
    ∀ t (φ : StrongDual ℝ E),
      Tendsto (fun n => φ (fseq n t)) atTop (𝓝 (φ (f t))) := by
  intro t φ
  have h := (RCLike.reCLM.continuous.tendsto (φ.extendTo𝕜' (f t))).comp
    (hweak t φ.extendTo𝕜')
  have heq (x : E) : RCLike.re (φ.extendTo𝕜' x : 𝕜) = φ x :=
    φ.toLinearMap.extendTo𝕜'_apply_re x
  change Tendsto (fun n => RCLike.re (φ.extendTo𝕜' (fseq n t) : 𝕜)) atTop
    (𝓝 (RCLike.re (φ.extendTo𝕜' (f t) : 𝕜))) at h
  simpa only [heq] using h

/-- Parameter tail convexification over either field with the original weak
convergence hypothesis. Coefficients are the real convex weights. -/
theorem parameter_tail_convexification_rclike
    (fseq : ℕ → C(K, E)) (C : ℝ) (hbound : ∀ n, ‖fseq n‖ ≤ C)
    (f : K → E)
    (hweak : ∀ t (φ : StrongDual 𝕜 E),
      Tendsto (fun n => φ (fseq n t)) atTop (𝓝 (φ (f t))))
    (hBaire : IsNormBaireOne f) :
    ∃ (F : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ),
      (∀ k n, 0 ≤ a k n) ∧ (∀ k, ∑ n ∈ F k, a k n = 1) ∧
      (∀ k n, n ∈ F k → k ≤ n) ∧
      ∀ t, Tendsto (fun k => ∑ n ∈ F k, a k n • fseq n t) atTop (𝓝 (f t)) :=
  parameter_tail_convexification fseq C hbound f
    (weak_pointwise_real_tests fseq f hweak) hBaire

end SurveyStatements.P4
