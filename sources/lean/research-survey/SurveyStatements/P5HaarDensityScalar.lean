import SurveyStatements.P5HaarDensityAlgebra

/-! The closed one-variable Haar span contains every scalar Lp vector with
zero mean. Its proof uses dyadic density, not a Haar-basis assumption. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def haarDensityScalarSpan : Submodule 𝕜 (Lp 𝕜 p unitIntervalMeasure) :=
  Submodule.span 𝕜 (Set.range (dyadicHaar 𝕜 p))

def haarDensityCenter : Lp 𝕜 p unitIntervalMeasure →L[𝕜] Lp 𝕜 p unitIntervalMeasure :=
  ContinuousLinearMap.id 𝕜 _ - probabilityLpMean

theorem haarDensityCenter_apply (f : Lp 𝕜 p unitIntervalMeasure) :
    haarDensityCenter f = f - probabilityLpMean (𝕜 := 𝕜) f := rfl

theorem haarDensityCenter_const (c : 𝕜) :
    haarDensityCenter (Lp.const p unitIntervalMeasure c) = 0 := by
  rw [haarDensityCenter_apply, probabilityLpMean_const, sub_self]

theorem haarDensityCenter_haar (I : DyadicIndex) :
    haarDensityCenter (dyadicHaar 𝕜 p I) = dyadicHaar 𝕜 p I := by
  rw [haarDensityCenter_apply, dyadicHaar_mean_zero, sub_zero]

theorem haarDensityCenter_mem_closedSpan (hp : p ≠ ∞)
    (f : Lp 𝕜 p unitIntervalMeasure) :
    haarDensityCenter f ∈ (haarDensityScalarSpan (𝕜 := 𝕜) (p := p)).topologicalClosure := by
  let S := (haarDensityScalarSpan (𝕜 := 𝕜) (p := p)).topologicalClosure
  let M := S.comap haarDensityCenter.toLinearMap
  have hclosed : IsClosed (M : Set (Lp 𝕜 p unitIntervalMeasure)) :=
    (Submodule.isClosed_topologicalClosure _).preimage haarDensityCenter.continuous
  have haug : haarDensityAugmentedSpan (𝕜 := 𝕜) (p := p) ≤ M := by
    apply Submodule.span_le.mpr
    intro x hx
    change haarDensityCenter x ∈ S
    rcases hx with rfl | ⟨I, rfl⟩
    · rw [haarDensityCenter_const]
      exact S.zero_mem
    · rw [haarDensityCenter_haar]
      exact (haarDensityScalarSpan (𝕜 := 𝕜) (p := p)).le_topologicalClosure
        (Submodule.subset_span ⟨I, rfl⟩)
  have htop := Submodule.topologicalClosure_minimal _ haug hclosed
  rw [haarDensityAugmentedSpan_closure hp] at htop
  exact htop (show f ∈ (⊤ : Submodule 𝕜 (Lp 𝕜 p unitIntervalMeasure)) from trivial)

theorem haarDensity_meanZero_mem_closedSpan (hp : p ≠ ∞)
    (f : Lp 𝕜 p unitIntervalMeasure) (hf : probabilityLpMean (𝕜 := 𝕜) f = 0) :
    f ∈ (haarDensityScalarSpan (𝕜 := 𝕜) (p := p)).topologicalClosure := by
  simpa only [haarDensityCenter_apply, hf, sub_zero] using haarDensityCenter_mem_closedSpan hp f

end SurveyStatements.P5
