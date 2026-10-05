import ThesisCommon.Analysis.L1UniformIntegrableWeakCompact
import ThesisCommon.Analysis.UniformIntegrableDomination
import ThesisCommon.Analysis.ComplexL1Coordinates
import ThesisCommon.Analysis.WeakCompactRestrictScalars

/-! The sufficient Dunford-Pettis direction for actual complex L1.
Real and imaginary coordinates give compact covers in their weak topologies;
the proved equality of scalar-restricted weak topologies reassembles them. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Pointwise
namespace ThesisCommon
variable {Y I : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem uniformIntegrable_complexL1Re {f : I → Lp ℂ 1 ν}
    (hUI : UniformIntegrable (fun i => (f i : Y → ℂ)) 1 ν) :
    UniformIntegrable (fun i => (complexL1Re ν (f i) : Y → ℝ)) 1 ν := by
  apply uniformIntegrable_of_ae_norm_le hUI
    (fun i => Lp.aestronglyMeasurable (complexL1Re ν (f i)))
  intro i
  filter_upwards [complexL1Re_coe (f i)] with y hy
  rw [hy, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem uniformIntegrable_complexL1Im {f : I → Lp ℂ 1 ν}
    (hUI : UniformIntegrable (fun i => (f i : Y → ℂ)) 1 ν) :
    UniformIntegrable (fun i => (complexL1Im ν (f i) : Y → ℝ)) 1 ν := by
  apply uniformIntegrable_of_ae_norm_le hUI
    (fun i => Lp.aestronglyMeasurable (complexL1Im ν (f i)))
  intro i
  filter_upwards [complexL1Im_coe (f i)] with y hy
  rw [hy, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm _

theorem isCompact_weakClosure_range_of_complex_uniformIntegrable
    [IsFiniteMeasure ν] (f : I → Lp ℂ 1 ν)
    (hUI : UniformIntegrable (fun i => (f i : Y → ℂ)) 1 ν) :
    IsCompact (closure (toWeakSpace ℂ (Lp ℂ 1 ν) '' Set.range f)) := by
  letI : T2Space (WeakSpace ℂ (Lp ℂ 1 ν)) :=
    (isEmbedding_weakBidualInclusion (𝕜 := ℂ) (E := Lp ℂ 1 ν)).t2Space
  let Kr := closure (toWeakSpace ℝ (Lp ℝ 1 ν) '' Set.range (fun i => complexL1Re ν (f i)))
  let Ki := closure (toWeakSpace ℝ (Lp ℝ 1 ν) '' Set.range (fun i => complexL1Im ν (f i)))
  have hr : IsCompact Kr := isCompact_weakClosure_range_of_uniformIntegrable
    (fun i => complexL1Re ν (f i)) (uniformIntegrable_complexL1Re hUI)
  have hi : IsCompact Ki := isCompact_weakClosure_range_of_uniformIntegrable
    (fun i => complexL1Im ν (f i)) (uniformIntegrable_complexL1Im hUI)
  let j : WeakSpace ℝ (Lp ℝ 1 ν) → WeakSpace ℂ (Lp ℂ 1 ν) :=
    fun x => (weakSpaceRealHomeomorph (𝕜 := ℂ) (E := Lp ℂ 1 ν)).symm
      (WeakSpace.map (complexL1OfReal ν) x)
  have hj : Continuous j := (weakSpaceRealHomeomorph (𝕜 := ℂ) (E := Lp ℂ 1 ν)).symm.continuous.comp
    (WeakSpace.map (complexL1OfReal ν)).continuous
  let K := j '' Kr + (fun x => Complex.I • j x) '' Ki
  have hK : IsCompact K := (hr.image hj).add (hi.image (continuous_const.smul hj))
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have hm := Set.add_mem_add
    (show j (toWeakSpace ℝ (Lp ℝ 1 ν) (complexL1Re ν (f i))) ∈ j '' Kr from
      ⟨_, subset_closure ⟨_, Set.mem_range_self i, rfl⟩, rfl⟩)
    (show Complex.I • j (toWeakSpace ℝ (Lp ℝ 1 ν) (complexL1Im ν (f i))) ∈
        (fun x => Complex.I • j x) '' Ki from
      ⟨_, subset_closure ⟨_, Set.mem_range_self i, rfl⟩, rfl⟩)
  change toWeakSpace ℂ (Lp ℂ 1 ν)
    (complexL1OfReal ν (complexL1Re ν (f i)) + Complex.I • complexL1OfReal ν (complexL1Im ν (f i))) ∈ K at hm
  simpa only [complexL1_decomposition] using hm

end ThesisCommon
