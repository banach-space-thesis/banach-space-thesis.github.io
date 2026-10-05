import ThesisCommon.Analysis.SigmaL1Partition
import ThesisCommon.Analysis.CoordinateMasks

/-! Coordinate suppressions are genuine measurable band cuts in the
arbitrary coproduct L1 model. Finite coordinate tails tend to zero. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 I Z : Type*} [RCLike 𝕜] [MeasurableSpace Z]

def sigmaIndexSet (A : Set I) : Set (Sigma (fun _ : I => Z)) := {z | z.1 ∈ A}

theorem sigmaIndexSet_measurable (A : Set I) : MeasurableSet (sigmaIndexSet (Z := Z) A) := by
  apply (sigmaSet_measurable_iff _).mpr
  intro i
  by_cases hi : i ∈ A
  · have he : Sigma.mk i ⁻¹' sigmaIndexSet (Z := Z) A = univ := by ext z; simp [sigmaIndexSet, hi]
    rw [he]; exact MeasurableSet.univ
  · have he : Sigma.mk i ⁻¹' sigmaIndexSet (Z := Z) A = ∅ := by ext z; simp [sigmaIndexSet, hi]
    rw [he]; exact MeasurableSet.empty

theorem sigmaL1PartitionEquiv_cut (ν : Measure Z) (A : Set I)
    (f : Lp 𝕜 1 (sigmaMeasure (fun _ : I => ν))) :
    sigmaL1PartitionEquiv (𝕜 := 𝕜) (fun _ : I => ν)
      (lpCut (sigmaIndexSet A) (sigmaIndexSet_measurable A) f) =
        lpCoordinateProjection (𝕜 := 𝕜) 1 A (sigmaL1PartitionEquiv (𝕜 := 𝕜) (fun _ : I => ν) f) := by
  classical
  apply lp.ext
  funext i
  rw [lpCoordinateProjection_apply]
  simp only [sigmaL1PartitionEquiv_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    apply congrArg (sigmaL1ComponentEquiv (𝕜 := 𝕜) (fun _ : I => ν) i)
    apply Lp.ext
    filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) (sigmaMeasureFiber i)
      (lpCut (sigmaIndexSet A) (sigmaIndexSet_measurable A) f),
      lebesgueLpRestrict_coe (𝕜 := 𝕜) (sigmaMeasureFiber i) f,
      ae_restrict_of_ae (lpCut_coe (sigmaIndexSet A) (sigmaIndexSet_measurable A) f),
      ae_restrict_mem (sigmaMeasureFiber_measurable (X := fun _ : I => Z) i)] with z h1 h2 h3 hz
    obtain ⟨w, rfl⟩ := hz
    rw [h1, h3, h2]
    exact indicator_of_mem (show Sigma.mk i w ∈ sigmaIndexSet (Z := Z) A from hi)
      (f : Sigma (fun _ : I => Z) → 𝕜)
  · rw [if_neg hi, ← map_zero (sigmaL1ComponentEquiv (𝕜 := 𝕜) (fun _ : I => ν) i)]
    apply congrArg (sigmaL1ComponentEquiv (𝕜 := 𝕜) (fun _ : I => ν) i)
    apply Lp.ext
    filter_upwards [lebesgueLpRestrict_coe (𝕜 := 𝕜) (sigmaMeasureFiber i)
      (lpCut (sigmaIndexSet A) (sigmaIndexSet_measurable A) f),
      ae_restrict_of_ae (lpCut_coe (sigmaIndexSet A) (sigmaIndexSet_measurable A) f),
      ae_restrict_mem (sigmaMeasureFiber_measurable (X := fun _ : I => Z) i),
      Lp.coeFn_zero 𝕜 1 ((sigmaMeasure (fun _ : I => ν)).restrict (sigmaMeasureFiber i))]
      with z h1 h2 hz h0
    obtain ⟨w, rfl⟩ := hz
    rw [h1, h2, h0]
    exact indicator_of_notMem (show Sigma.mk i w ∉ sigmaIndexSet (Z := Z) A from hi)
      (f : Sigma (fun _ : I => Z) → 𝕜)

theorem ellOne_finite_tail_small {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : lp (fun _ : I => E) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset I, ‖lpCoordinateProjection (𝕜 := 𝕜) 1 (↑F : Set I)ᶜ x‖ < ε := by
  classical
  obtain ⟨F, hF⟩ := (Metric.tendsto_nhds.mp (lp.hasSum_single (by simp) x) ε hε).exists
  have he : lpCoordinateProjection (𝕜 := 𝕜) 1 (↑F : Set I)ᶜ x =
      x - ∑ i ∈ F, lp.single 1 i (x i) := by
    apply lp.ext
    funext i
    simp only [lpCoordinateProjection_apply, mem_compl_iff, Finset.mem_coe,
      lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
      Finset.sum_pi_single]
    by_cases hi : i ∈ F <;> simp [hi]
  refine ⟨F, ?_⟩
  rw [he, ← dist_eq_norm, dist_comm]
  exact hF

end ThesisCommon
