import BanachIsometric.RadialMomentScaling
import BanachIsometric.StarBodyBoundary

/-!
# Actual positive levels of the same homogeneous gauge

Every positive level body is the actual positive homothety of the unit body.
Compactness, frontier nullity, and exact weighted-volume scaling are proved
for these levels without a convexity or symmetry hypothesis.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsDefinitePositiveHomogeneous.div_const {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) {r : ℝ} (hr : 0 < r) :
    IsDefinitePositiveHomogeneous (fun x => g x / r) where
  nonneg x := div_nonneg (hg.nonneg x) hr.le
  eq_zero_iff x := by simp only [div_eq_zero_iff, hr.ne', or_false, hg.eq_zero_iff]
  smul_nonneg t ht x := by rw [hg.smul_nonneg t ht]; ring

theorem IsDefinitePositiveHomogeneous.sublevel_eq_pos_smul_unit {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) {r : ℝ} (hr : 0 < r) :
    {x | g x ≤ r} = r • {x | g x ≤ 1} := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  change g x ≤ r ↔ g (r⁻¹ • x) ≤ 1
  rw [hg.smul_nonneg r⁻¹ (inv_nonneg.mpr hr.le)]
  simpa only [div_eq_inv_mul] using (div_le_one hr : g x / r ≤ 1 ↔ g x ≤ r).symm

variable [FiniteDimensional ℝ E]

theorem IsDefinitePositiveHomogeneous.isCompact_sublevel_of_continuous {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) :
    IsCompact {x | g x ≤ 1} := by
  obtain ⟨ε, _, hε, _, hbound⟩ := hg.exists_norm_comparison hcont.continuousOn
  apply (isCompact_closedBall (0 : E) (1 / ε)).of_isClosed_subset
    (isClosed_le hcont continuous_const)
  intro x hx
  change g x ≤ 1 at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (le_div_iff₀ hε).mpr
  nlinarith [(hbound x).1]

theorem IsDefinitePositiveHomogeneous.isCompact_pos_sublevel {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) {r : ℝ} (hr : 0 < r) :
    IsCompact {x | g x ≤ r} := by
  have he : {x | g x / r ≤ 1} = {x | g x ≤ r} := by
    ext x
    exact div_le_one hr
  rw [← he]
  exact (hg.div_const hr).isCompact_sublevel_of_continuous (hcont.div_const r)

omit [FiniteDimensional ℝ E] in
theorem IsDefinitePositiveHomogeneous.frontier_pos_sublevel_eq_level {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) {r : ℝ} (hr : 0 < r) :
    frontier {x | g x ≤ r} = {x | g x = r} := by
  have he : {x | g x / r ≤ 1} = {x | g x ≤ r} := by ext x; exact div_le_one hr
  have hf := (hg.div_const hr).frontier_sublevel_eq_level (hcont.div_const r)
  rw [he] at hf
  have hlevel : {x | g x / r = 1} = {x | g x = r} := by
    ext x
    simpa only [one_mul] using (div_eq_iff hr.ne' : g x / r = 1 ↔ g x = 1 * r)
  rwa [hlevel] at hf

omit [FiniteDimensional ℝ E] in
theorem IsDefinitePositiveHomogeneous.interior_pos_sublevel_eq_strict {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) {r : ℝ} (hr : 0 < r) :
    interior {x | g x ≤ r} = {x | g x < r} := by
  ext x
  constructor
  · intro hx
    have hxK : x ∈ {z : E | g z ≤ r} := interior_subset hx
    have hle : g x ≤ r := hxK
    apply lt_of_le_of_ne hle
    intro he
    have hb : x ∈ frontier {x | g x ≤ r} := by
      rw [hg.frontier_pos_sublevel_eq_level hcont hr]
      exact he
    exact hb.2 hx
  · intro hx
    have hopen : IsOpen {z : E | g z < r} := isOpen_lt hcont continuous_const
    have hsub : {x | g x < r} ⊆ interior {x | g x ≤ r} :=
      hopen.subset_interior_iff.mpr (by
        intro z hz
        exact (show g z < r from hz).le)
    exact hsub hx

variable [MeasurableSpace E] [BorelSpace E]

theorem measure_frontier_pos_sublevel_eq_zero
    (μ : Measure E) [μ.IsAddHaarMeasure] {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) {r : ℝ} (hr : 0 < r) :
    μ (frontier {x | g x ≤ r}) = 0 := by
  have he : {x | g x / r ≤ 1} = {x | g x ≤ r} := by ext x; exact div_le_one hr
  rw [← he]
  exact measure_frontier_sublevel_eq_zero μ (hg.div_const hr) (hcont.div_const r)
    ((hg.div_const hr).isCompact_sublevel_of_continuous (hcont.div_const r))

theorem integral_norm_pow_pos_sublevel
    (μ : Measure E) [μ.IsAddHaarMeasure] {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x in {x | g x ≤ r}, ‖x‖ ^ m ∂μ) =
      r ^ (Module.finrank ℝ E + m) * ∫ x in {x | g x ≤ 1}, ‖x‖ ^ m ∂μ := by
  rw [hg.sublevel_eq_pos_smul_unit hr]
  exact integral_norm_pow_smul_set μ {x | g x ≤ 1} m hr

theorem integral_norm_pow_unit_sublevel_pos [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {g : E → ℝ}
    (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g) (m : ℕ) :
    0 < ∫ x in {x | g x ≤ 1}, ‖x‖ ^ m ∂μ :=
  integral_norm_pow_pos_of_zero_mem_interior μ (hg.isCompact_sublevel_of_continuous hcont)
    (hg.zero_mem_interior_sublevel hcont.continuousOn) m

end BanachIsometric
