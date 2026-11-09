import SurveyStatements.P5HaarDensityScalar
import SurveyStatements.P5HaarDensityTensor

/-! The genuine identification of the closed product-Haar span with the
intersection of the two expectation kernels. The density proof works for
every finite exponent at least one. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem haarDensityIndicator_tensor (I : DyadicIndex)
    (g : Lp 𝕜 1 unitIntervalMeasure) :
    haarDensityIndicator (p := p) I g =
      tensorWith g (haarDensityIndicator (p := p) I (1 : 𝕜)) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := p)
      (hs := (show MeasurableSet (haarDensityCell I) from measurableSet_Ico))
      (hμs := measure_ne_top unitIntervalMeasure _) (c := g),
    tensorWith_ae g (haarDensityIndicator (p := p) I (1 : 𝕜)),
    indicatorConstLp_coeFn (p := p)
      (hs := (show MeasurableSet (haarDensityCell I) from measurableSet_Ico))
      (hμs := measure_ne_top unitIntervalMeasure _) (c := (1 : 𝕜))]
    with x hleft htensor hright
  change haarDensityIndicator (p := p) I g x = _ at hleft
  change haarDensityIndicator (p := p) I (1 : 𝕜) x = _ at hright
  change haarDensityIndicator (p := p) I g x =
    tensorWith g (haarDensityIndicator (p := p) I (1 : 𝕜)) x
  rw [hleft, htensor, hright]
  by_cases hx : x ∈ haarDensityCell I <;> simp [hx]

theorem haarDensity_cancellativeProjection_mem_productHaarSpace (hp : p ≠ ∞)
    (f : MixedNorm 𝕜 p) :
    twoKernelProjection (outerExpectation 𝕜 p) (innerExpectation 𝕜 p) f ∈
      ProductHaarSpace 𝕜 p := by
  let P := twoKernelProjection (outerExpectation 𝕜 p) (innerExpectation 𝕜 p)
  let M := (ProductHaarSpace 𝕜 p).comap P.toLinearMap
  have hclosed : IsClosed (M : Set (MixedNorm 𝕜 p)) :=
    (Submodule.isClosed_topologicalClosure _).preimage P.continuous
  have hstep : haarDensityStepSpace (𝕜 := 𝕜)
      (E := Lp 𝕜 1 unitIntervalMeasure) (p := p) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨I, g⟩, rfl⟩
    change twoKernelProjection (outerExpectation 𝕜 p) (innerExpectation 𝕜 p)
      (haarDensityIndicator (p := p) I g) ∈ ProductHaarSpace 𝕜 p
    rw [haarDensityIndicator_tensor, haarDensity_projection_tensor]
    apply haarDensity_tensor_closedSpan
    · exact haarDensityCenter_mem_closedSpan (by norm_num : (1 : ℝ≥0∞) ≠ ∞) g
    · exact haarDensityCenter_mem_closedSpan hp (haarDensityIndicator (p := p) I (1 : 𝕜))
  have htop := Submodule.topologicalClosure_minimal _ hstep hclosed
  rw [haarDensityStepSpace_closure_eq_top hp] at htop
  exact htop (show f ∈ (⊤ : Submodule 𝕜 (MixedNorm 𝕜 p)) from trivial)

theorem doublyZeroMean_le_productHaarSpace (hp : p ≠ ∞) :
    DoublyZeroMean 𝕜 p ≤ ProductHaarSpace 𝕜 p := by
  intro f hf
  have hfix : twoKernelProjection (outerExpectation 𝕜 p) (innerExpectation 𝕜 p) f = f :=
    twoKernelProjection_fixes _ _ ⟨f, hf⟩
  rw [← hfix]
  exact haarDensity_cancellativeProjection_mem_productHaarSpace hp f

/-- The source's closed product-Haar span is precisely the actual doubly
zero-mean subspace of the mixed Bochner space. -/
theorem productHaarSpace_eq_doublyZeroMean (hp : p ≠ ∞) :
    ProductHaarSpace 𝕜 p = DoublyZeroMean 𝕜 p :=
  le_antisymm (productHaarSpace_le_doublyZeroMean 𝕜 p)
    (doublyZeroMean_le_productHaarSpace hp)

end SurveyStatements.P5
