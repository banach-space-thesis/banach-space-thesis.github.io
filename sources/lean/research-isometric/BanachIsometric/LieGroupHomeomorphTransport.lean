import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Actual manifold and Lie-group structures transport across a continuous
multiplicative equivalence, keeping the source's original topology. Charts
are the actual pullbacks of target charts; their transition maps are exactly
the old transition maps. -/

noncomputable section
namespace BanachIsometric
open Set
open scoped Topology Manifold

section Topology
variable {E G H : Type*} [TopologicalSpace E] [TopologicalSpace G] [TopologicalSpace H]
  [ChartedSpace E H]

def homeomorphPullbackChartedSpace (h : G ≃ₜ H) : ChartedSpace E G where
  atlas := h.transOpenPartialHomeomorph '' atlas E H
  chartAt x := h.transOpenPartialHomeomorph (chartAt E (h x))
  mem_chart_source x := mem_chart_source E (h x)
  chart_mem_atlas x := ⟨chartAt E (h x), chart_mem_atlas E (h x), rfl⟩

omit [ChartedSpace E H] in
theorem homeomorph_pullback_transition (h : G ≃ₜ H)
    (c d : OpenPartialHomeomorph H E) :
    (h.transOpenPartialHomeomorph c).symm.trans (h.transOpenPartialHomeomorph d) =
      c.symm.trans d := by
  apply OpenPartialHomeomorph.ext
  · intro z
    change d (h (h.symm (c.symm z))) = d (c.symm z)
    rw [h.apply_symm_apply]
  · intro z
    change c (h (h.symm (d.symm z))) = c (d.symm z)
    rw [h.apply_symm_apply]
  · ext z
    change (z ∈ c.target ∧ h (h.symm (c.symm z)) ∈ d.source) ↔
      (z ∈ c.target ∧ c.symm z ∈ d.source)
    rw [h.apply_symm_apply]

end Topology

section Manifold
variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [TopologicalSpace H] [ChartedSpace E H]
  {n : WithTop ℕ∞}

theorem homeomorphPullback_isManifold (h : G ≃ₜ H)
    [IsManifold (modelWithCornersSelf ℝ E) n H] :
    letI := homeomorphPullbackChartedSpace (E := E) h
    IsManifold (modelWithCornersSelf ℝ E) n G := by
  letI := homeomorphPullbackChartedSpace (E := E) h
  refine { compatible := ?_ }
  intro c d hc hd
  change c ∈ h.transOpenPartialHomeomorph '' atlas E H at hc
  change d ∈ h.transOpenPartialHomeomorph '' atlas E H at hd
  obtain ⟨c, hc, rfl⟩ := hc
  obtain ⟨d, hd, rfl⟩ := hd
  rw [homeomorph_pullback_transition]
  exact (contDiffGroupoid n (modelWithCornersSelf ℝ E)).compatible hc hd

theorem contMDiff_homeomorphPullback (h : G ≃ₜ H) :
    letI := homeomorphPullbackChartedSpace (E := E) h
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n h := by
  letI := homeomorphPullbackChartedSpace (E := E) h
  intro x
  rw [contMDiffAt_iff]
  refine ⟨h.continuous.continuousAt, ?_⟩
  let c := chartAt E (h x)
  change ContDiffWithinAt ℝ n (fun z => c (h (h.symm (c.symm z)))) _ (c (h x))
  simp only [h.apply_symm_apply]
  have hmem : c (h x) ∈ c.target := c.map_source (mem_chart_source E (h x))
  exact (contDiffAt_id.congr_of_eventuallyEq (c.eventually_right_inverse hmem)).contDiffWithinAt

theorem contMDiff_symm_homeomorphPullback (h : G ≃ₜ H) :
    letI := homeomorphPullbackChartedSpace (E := E) h
    ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n h.symm := by
  letI := homeomorphPullbackChartedSpace (E := E) h
  intro y
  rw [contMDiffAt_iff]
  refine ⟨h.symm.continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ n (fun z => (chartAt E (h (h.symm y)))
    (h (h.symm ((chartAt E y).symm z)))) _ ((chartAt E y) y)
  simp only [h.apply_symm_apply]
  have hmem : chartAt E y y ∈ (chartAt E y).target :=
    (chartAt E y).map_source (mem_chart_source E y)
  exact (contDiffAt_id.congr_of_eventuallyEq
    ((chartAt E y).eventually_right_inverse hmem)).contDiffWithinAt

end Manifold

section Group
variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [ChartedSpace E H]
  {n : WithTop ℕ∞}

def mulEquivHomeomorph (e : G ≃* H) (he : Continuous e) (hi : Continuous e.symm) : G ≃ₜ H where
  toEquiv := e.toEquiv
  continuous_toFun := he
  continuous_invFun := hi

theorem lieGroup_homeomorphPullback (e : G ≃* H)
    (he : Continuous e) (hi : Continuous e.symm)
    [LieGroup (modelWithCornersSelf ℝ E) n H] :
    letI := homeomorphPullbackChartedSpace (E := E) (mulEquivHomeomorph e he hi)
    LieGroup (modelWithCornersSelf ℝ E) n G := by
  let h := mulEquivHomeomorph e he hi
  letI := homeomorphPullbackChartedSpace (E := E) h
  have hf : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n h :=
    contMDiff_homeomorphPullback h
  have hb : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n h.symm :=
    contMDiff_symm_homeomorphPullback h
  refine {
    toContMDiffMul := {
      toIsManifold := homeomorphPullback_isManifold h
      contMDiff_mul := ?_ }
    contMDiff_inv := ?_ }
  · have hm := hb.comp ((contMDiff_mul (modelWithCornersSelf ℝ E) n).comp (hf.prodMap hf))
    change ContMDiff ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ E) n (fun p : G × G => e.symm (e p.1 * e p.2)) at hm
    simpa only [← e.map_mul, e.symm_apply_apply] using hm
  · have hm := hb.comp ((contMDiff_inv (modelWithCornersSelf ℝ E) n).comp hf)
    change ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) n
      (fun x : G => e.symm ((e x)⁻¹)) at hm
    simpa only [← e.map_inv, e.symm_apply_apply] using hm

end Group
end BanachIsometric
