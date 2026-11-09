import SurveyStatements.P5HaarNorm

/-! Continuity in both tensor factors, and the action of the cancellative
projection on elementary tensors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ENNReal

namespace SurveyStatements.P5

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def haarDensityTensorRight (x : Lp 𝕜 p unitIntervalMeasure) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] MixedNorm 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := fun g => tensorWith g x
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [tensorWith_ae (g + h) x, tensorWith_ae g x, tensorWith_ae h x,
          Lp.coeFn_add (tensorWith g x) (tensorWith h x)] with s hsum hg hh ha
        rw [hsum, ha]
        simp only [Pi.add_apply]
        rw [hg, hh, smul_add]
      map_smul' := by
        intro a g
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [tensorWith_ae (a • g) x, tensorWith_ae g x,
          Lp.coeFn_smul a (tensorWith g x)] with s hleft hg hright
        rw [hleft, hright]
        simp only [Pi.smul_apply]
        rw [hg]
        simp only [smul_smul, mul_comm, RingHom.id_apply] }
    ‖x‖ (by
      intro g
      exact le_of_eq ((norm_tensorWith 𝕜 p g x).trans (mul_comm _ _)))

theorem haarDensityTensorRight_apply (x : Lp 𝕜 p unitIntervalMeasure)
    (g : Lp 𝕜 1 unitIntervalMeasure) : haarDensityTensorRight x g = tensorWith g x := rfl

theorem haarDensity_tensor_sub_inner (g h : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure) :
    tensorWith (g - h) x = tensorWith g x - tensorWith h x :=
  (haarDensityTensorRight x).map_sub g h

theorem haarDensity_projection_tensor (g : Lp 𝕜 1 unitIntervalMeasure)
    (x : Lp 𝕜 p unitIntervalMeasure) :
    twoKernelProjection (outerExpectation 𝕜 p) (innerExpectation 𝕜 p) (tensorWith g x) =
      tensorWith (g - probabilityLpMean (𝕜 := 𝕜) g)
        (x - probabilityLpMean (𝕜 := 𝕜) x) := by
  change (tensorWith g x - innerExpectation 𝕜 p (tensorWith g x)) -
    outerExpectation 𝕜 p (tensorWith g x - innerExpectation 𝕜 p (tensorWith g x)) = _
  rw [innerExpectation_tensor, map_sub, outerExpectation_tensor, outerExpectation_tensor]
  rw [map_sub, haarDensity_tensor_sub_inner, haarDensity_tensor_sub_inner]

theorem haarDensity_map_closedSpan {V W ι : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (L : V →L[𝕜] W) (S : Submodule 𝕜 W) (hS : IsClosed (S : Set W))
    (v : ι → V) {x : V} (hx : x ∈ (Submodule.span 𝕜 (range v)).topologicalClosure)
    (hv : ∀ i, L (v i) ∈ S) : L x ∈ S := by
  let M := S.comap L.toLinearMap
  have hm : Submodule.span 𝕜 (range v) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hv i
  exact Submodule.topologicalClosure_minimal _ hm (hS.preimage L.continuous) hx

theorem haarDensity_tensor_closedSpan
    (g : Lp 𝕜 1 unitIntervalMeasure) (x : Lp 𝕜 p unitIntervalMeasure)
    (hg : g ∈ (Submodule.span 𝕜 (range (dyadicHaar 𝕜 1))).topologicalClosure)
    (hx : x ∈ (Submodule.span 𝕜 (range (dyadicHaar 𝕜 p))).topologicalClosure) :
    tensorWith g x ∈ ProductHaarSpace 𝕜 p := by
  refine haarDensity_map_closedSpan (tensorWith g) (ProductHaarSpace 𝕜 p)
    (Submodule.isClosed_topologicalClosure _) (dyadicHaar 𝕜 p) hx ?_
  intro I
  refine haarDensity_map_closedSpan (haarDensityTensorRight (dyadicHaar 𝕜 p I))
    (ProductHaarSpace 𝕜 p) (Submodule.isClosed_topologicalClosure _)
    (dyadicHaar 𝕜 1) hg ?_
  intro J
  exact (Submodule.span 𝕜 (range (fun IJ : DyadicIndex × DyadicIndex =>
    productHaar 𝕜 p IJ.1 IJ.2))).le_topologicalClosure
      (Submodule.subset_span ⟨(I, J), rfl⟩)

end SurveyStatements.P5
