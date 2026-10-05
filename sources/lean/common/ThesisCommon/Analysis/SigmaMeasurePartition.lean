import ThesisCommon.Analysis.DecomposableLpPartition
import ThesisCommon.Analysis.LpMeasureCoding
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! Arbitrary coproducts of measure spaces, with their piecewise sigma
algebra. Each fiber is a measurable embedded copy and the measure restricts
exactly to the corresponding pushed-forward measure. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Function
namespace ThesisCommon
variable {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]

theorem sigmaSet_measurable_iff (A : Set (Sigma X)) :
    MeasurableSet A ↔ ∀ i, MeasurableSet (Sigma.mk i ⁻¹' A) :=
  MeasurableSpace.measurableSet_iInf

theorem measurable_sigmaMk (i : I) : Measurable (Sigma.mk i : X i → Sigma X) := by
  intro A hA
  exact (sigmaSet_measurable_iff A).mp hA i

theorem measurableEmbedding_sigmaMk (i : I) :
    MeasurableEmbedding (Sigma.mk i : X i → Sigma X) where
  injective := sigma_mk_injective
  measurable := measurable_sigmaMk i
  measurableSet_image' := by
    intro A hA
    apply (sigmaSet_measurable_iff _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Set.preimage_image_eq _ sigma_mk_injective] using hA
    · have he : Sigma.mk j ⁻¹' (Sigma.mk i '' A) = ∅ := by
        ext x
        simp only [mem_preimage, mem_image, mem_empty_iff_false, iff_false]
        rintro ⟨y, _, hy⟩
        exact hji (congrArg Sigma.fst hy).symm
      rw [he]
      exact MeasurableSet.empty

def sigmaMeasure (μ : ∀ i, Measure (X i)) : Measure (Sigma X) :=
  Measure.sum (fun i => (μ i).map (Sigma.mk i))

def sigmaMeasureFiber (i : I) : Set (Sigma X) := range (Sigma.mk i)

theorem sigmaMeasureFiber_measurable (i : I) : MeasurableSet (sigmaMeasureFiber (X := X) i) :=
  (measurableEmbedding_sigmaMk i).measurableSet_range

theorem sigmaMeasureFiber_disjoint : Pairwise (Disjoint on (sigmaMeasureFiber (X := X))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  exact hij (congrArg Sigma.fst hb).symm

theorem sigmaMeasureFiber_iUnion : (⋃ i, sigmaMeasureFiber (X := X) i) = univ := by
  ext ⟨i, x⟩
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨i, x, rfl⟩

theorem sigmaMeasure_apply (μ : ∀ i, Measure (X i)) (A : Set (Sigma X))
    (hA : MeasurableSet A) : sigmaMeasure μ A = ∑' i, μ i (Sigma.mk i ⁻¹' A) := by
  rw [sigmaMeasure, Measure.sum_apply _ hA]
  apply tsum_congr
  intro i
  exact Measure.map_apply (measurable_sigmaMk i) hA

theorem sigmaMeasure_restrict_fiber (μ : ∀ i, Measure (X i)) (i : I) :
    (sigmaMeasure μ).restrict (sigmaMeasureFiber i) = (μ i).map (Sigma.mk i) := by
  ext A hA
  rw [Measure.restrict_apply hA, sigmaMeasure_apply _ _ (hA.inter (sigmaMeasureFiber_measurable i))]
  rw [tsum_eq_single i]
  · rw [Measure.map_apply (measurable_sigmaMk i) hA]
    congr 1
    ext x
    simp [sigmaMeasureFiber]
  · intro j hji
    have he : Sigma.mk j ⁻¹' (A ∩ sigmaMeasureFiber i) = ∅ := by
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨_, y, hy⟩
      exact hji (congrArg Sigma.fst hy).symm
    rw [he, measure_empty]

theorem sigmaMeasure_sum_restrict (μ : ∀ i, Measure (X i)) :
    Measure.sum (fun i => (sigmaMeasure μ).restrict (sigmaMeasureFiber i)) = sigmaMeasure μ := by
  simp_rw [sigmaMeasure_restrict_fiber]
  rfl

theorem sigmaMeasure_fiber (μ : ∀ i, Measure (X i)) (i : I) :
    sigmaMeasure μ (sigmaMeasureFiber i) = μ i univ := by
  have h := congrArg (fun m : Measure (Sigma X) => m univ) (sigmaMeasure_restrict_fiber μ i)
  simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.map_apply (measurable_sigmaMk i) MeasurableSet.univ, preimage_univ] using h

theorem sigmaMeasureFiber_injective [∀ i, Nonempty (X i)] :
    Function.Injective (sigmaMeasureFiber (X := X)) := by
  intro i j h
  obtain ⟨x⟩ := (inferInstance : Nonempty (X i))
  have hx : Sigma.mk i x ∈ sigmaMeasureFiber j := h ▸ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  exact (congrArg Sigma.fst hy).symm

end ThesisCommon
