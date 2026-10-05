import JLMS.PositiveRiesz

/-!
# Compact clopen cutoffs and density in C₀(K)

Vanishing at infinity gives a compact set outside which a function is small.
A compact clopen superset then provides a compactly supported approximation
in the supremum norm. These cutoffs make no countability assumption on K.
-/

noncomputable section

open Set Filter Topology
open scoped CompactlySupported

namespace JLMS

variable {K : Type*} [TopologicalSpace K]

/-- Truncation by a compact clopen cutoff, bundled in C_c(K). -/
def compactCutoffCC (f : CZero ℝ K) (U : Set K) (hU : IsClopen U)
    (hc : IsCompact U) : C_c(K, ℝ) where
  toContinuousMap := (f * clopenIndicator U hU hc).toContinuousMap
  hasCompactSupport' := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hU.isClosed
    intro x hx
    by_contra hxU
    exact hx (by change f x * clopenIndicator U hU hc x = 0; simp [hxU])

theorem compactSupportInclusion_cutoff (f : CZero ℝ K) (U : Set K)
    (hU : IsClopen U) (hc : IsCompact U) :
    compactSupportInclusion (compactCutoffCC f U hU hc) = f * clopenIndicator U hU hc := by
  ext x
  rfl

variable [LocallyCompactSpace K] [T2Space K]

/-- Compactly supported test functions approximate each C₀ function uniformly. -/
theorem exists_compactSupport_approx (hK : IsScattered K) (f : CZero ℝ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(K, ℝ), ‖f - compactSupportInclusion g‖ < ε := by
  have hev : {x | ‖f x‖ < ε / 2} ∈ cocompact K := by
    simpa only [dist_zero_right] using
      (Metric.tendsto_nhds.mp f.zero_at_infty' (ε / 2) (half_pos hε))
  obtain ⟨C, hC, hsmall⟩ := mem_cocompact.mp hev
  obtain ⟨U, hU, hc, hCU⟩ := exists_compact_clopen_superset hK hC
  refine ⟨compactCutoffCC f U hU hc, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  rw [compactSupportInclusion_cutoff]
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro x
  change ‖f x - f x * clopenIndicator U hU hc x‖ ≤ ε / 2
  by_cases hxU : x ∈ U
  · simp [hxU, (half_pos hε).le]
  · have hxC : x ∈ Cᶜ := fun hx => hxU (hCU hx)
    simpa [hxU] using (hsmall hxC).le

/-- Density of the inclusion, used to extend the compact-support Riesz formula. -/
theorem denseRange_compactSupportInclusion (hK : IsScattered K) :
    DenseRange (compactSupportInclusion (K := K)) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_compactSupport_approx hK f hε
  exact ⟨compactSupportInclusion g, mem_range_self g, by
    simpa only [dist_eq_norm, norm_sub_rev] using hg⟩

end JLMS
