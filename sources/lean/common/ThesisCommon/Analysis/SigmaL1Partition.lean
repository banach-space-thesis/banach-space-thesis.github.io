import ThesisCommon.Analysis.SigmaMeasurePartition
import ThesisCommon.Analysis.LpCodingOrder
import ThesisCommon.Analysis.LebesgueLpTransport
import ThesisCommon.Analysis.IntervalLpFunctionSelfSimilarity

/-! The actual L1 space of an arbitrary measure coproduct is linearly
isometric to the genuine dependent ℓ1 sum of its component L1 spaces. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜] {X : I → Type*} [∀ i, MeasurableSpace (X i)]

private theorem component_surjective (μ : ∀ i, Measure (X i)) (i : I) :
    Function.Surjective (Lp.compMeasurePreserving (Sigma.mk i)
      (⟨measurable_sigmaMk i, (sigmaMeasure_restrict_fiber μ i).symm⟩ :
        MeasurePreserving (Sigma.mk i) (μ i) ((sigmaMeasure μ).restrict (sigmaMeasureFiber i))) :
      Lp 𝕜 1 ((sigmaMeasure μ).restrict (sigmaMeasureFiber i)) → Lp 𝕜 1 (μ i)) := by
  intro g
  let hmp : MeasurePreserving (Sigma.mk i) (μ i) ((sigmaMeasure μ).restrict (sigmaMeasureFiber i)) :=
    ⟨measurable_sigmaMk i, (sigmaMeasure_restrict_fiber μ i).symm⟩
  have hg : StronglyMeasurable[(inferInstance : MeasurableSpace (Sigma X)).comap (Sigma.mk i)]
      (fun x => g x) := by
    rw [(measurableEmbedding_sigmaMk i).comap_eq]
    exact Lp.stronglyMeasurable g
  obtain ⟨h, hh, heq⟩ := hg.exists_eq_measurable_comp
  have hLp : MemLp h 1 ((sigmaMeasure μ).restrict (sigmaMeasureFiber i)) := by
    rw [← hmp.map_eq]
    apply (memLp_map_measure_iff hh.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr
    rw [← heq]
    exact Lp.memLp g
  refine ⟨hLp.toLp h, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving (hLp.toLp h) hmp,
    hmp.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hLp)] with x hx hy
  exact hx.trans (hy.trans (congrFun heq x).symm)

def sigmaL1ComponentEquiv (μ : ∀ i, Measure (X i)) (i : I) :
    Lp 𝕜 1 ((sigmaMeasure μ).restrict (sigmaMeasureFiber i)) ≃ₗᵢ[𝕜] Lp 𝕜 1 (μ i) :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ 𝕜 (Sigma.mk i)
    (⟨measurable_sigmaMk i, (sigmaMeasure_restrict_fiber μ i).symm⟩ :
      MeasurePreserving (Sigma.mk i) (μ i) ((sigmaMeasure μ).restrict (sigmaMeasureFiber i))))
    (component_surjective μ i)

def sigmaL1PartitionEquiv (μ : ∀ i, Measure (X i)) :
    Lp 𝕜 1 (sigmaMeasure μ) ≃ₗᵢ[𝕜] lp (fun i => Lp 𝕜 1 (μ i)) 1 :=
  (decomposableLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) (p := 1) (by norm_num) sigmaMeasureFiber sigmaMeasureFiber_measurable
    sigmaMeasureFiber_disjoint (sigmaMeasure_sum_restrict μ)).trans
    (lebesgueLpCoordinateEquiv (𝕜 := 𝕜) (p := 1) (by norm_num) (sigmaL1ComponentEquiv μ))

theorem sigmaL1PartitionEquiv_apply (μ : ∀ i, Measure (X i))
    (f : Lp 𝕜 1 (sigmaMeasure μ)) (i : I) :
    sigmaL1PartitionEquiv μ f i =
      sigmaL1ComponentEquiv μ i (lebesgueLpRestrict (𝕜 := 𝕜) (sigmaMeasureFiber i) f) := rfl

end ThesisCommon
