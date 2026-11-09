import BanachIsometric.MomentRegularity
import BanachIsometric.RadialStarBody
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Null boundaries of star bodies by homothetic squeezing

Contractions of a homogeneous unit sublevel lie in its interior. Its boundary
therefore lies in arbitrarily thin homothetic shells, whose Haar volumes tend
to zero. This proves the boundary-nullity input of Theorem 3.1 without using
Hausdorff measure or a Lipschitz parametrisation of the sphere.
-/

namespace BanachIsometric

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Pointwise

section Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The frontier of a continuous homogeneous unit sublevel is precisely its
unit level. No norm, convexity, or symmetry property of the gauge is used. -/
theorem IsDefinitePositiveHomogeneous.frontier_sublevel_eq_level {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) :
    frontier {x : V | p x ≤ 1} = {x : V | p x = 1} := by
  have hclosed : IsClosed {x : V | p x ≤ 1} := isClosed_le hcont continuous_const
  have hopen : IsOpen {x : V | p x < 1} := isOpen_lt hcont continuous_const
  have hstrict : {x : V | p x < 1} ⊆ interior {x : V | p x ≤ 1} :=
    hopen.subset_interior_iff.mpr (by intro x hx; exact (show p x < 1 from hx).le)
  ext x
  constructor
  · intro hx
    rw [hclosed.frontier_eq] at hx
    exact le_antisymm hx.1 (le_of_not_gt (fun hpx ↦ hx.2 (hstrict hpx)))
  · intro hpx
    change p x = 1 at hpx
    have h1 : (1 : ℝ) ∈ closure (Ioi (1 : ℝ)) := by
      rw [closure_Ioi]
      exact (le_rfl : (1 : ℝ) ≤ 1)
    have hmap : x ∈ closure ((fun t : ℝ ↦ t • x) '' Ioi (1 : ℝ)) := by
      simpa only [one_smul] using image_closure_subset_closure_image
        (continuous_id.smul continuous_const : Continuous (fun t : ℝ ↦ t • x))
        (mem_image_of_mem (fun t : ℝ ↦ t • x) h1)
    have himage : ((fun t : ℝ ↦ t • x) '' Ioi (1 : ℝ)) ⊆ {x : V | p x ≤ 1}ᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      change (1 : ℝ) < t at ht
      change ¬ p (t • x) ≤ 1
      rw [hp.smul_nonneg t (by linarith) x, hpx, mul_one]
      exact not_le_of_gt ht
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hpx.le, (closure_mono himage) hmap⟩

/-- Strict contractions send the whole closed body into its interior. -/
theorem IsDefinitePositiveHomogeneous.contract_sublevel_subset_interior {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    c • {x : V | p x ≤ 1} ⊆ interior {x : V | p x ≤ 1} := by
  have hopen : IsOpen {x : V | p x < 1} := isOpen_lt hcont continuous_const
  have hstrict : {x : V | p x < 1} ⊆ interior {x : V | p x ≤ 1} :=
    hopen.subset_interior_iff.mpr (by intro x hx; exact (show p x < 1 from hx).le)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_smul_set.mp hz
  apply hstrict
  change p (c • x) < 1
  rw [hp.smul_nonneg c hc0 x]
  calc
    c * p x ≤ c * 1 := mul_le_mul_of_nonneg_left hx hc0
    _ < 1 := by simpa only [mul_one] using hc1

/-- Every boundary point lies outside every strict homothetic contraction. -/
theorem IsDefinitePositiveHomogeneous.frontier_sublevel_subset_shell {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    frontier {x : V | p x ≤ 1} ⊆
      {x : V | p x ≤ 1} \ (c • {x : V | p x ≤ 1}) := by
  have hclosed : IsClosed {x : V | p x ≤ 1} := isClosed_le hcont continuous_const
  intro x hx
  rw [hclosed.frontier_eq] at hx
  exact ⟨hx.1, fun hscaled ↦
    hx.2 (hp.contract_sublevel_subset_interior hcont hc0 hc1 hscaled)⟩

/-- Positive level sets are scaled copies of the unit boundary. -/
theorem IsDefinitePositiveHomogeneous.mem_pos_smul_frontier_sublevel_iff {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (x : V) {r : ℝ} (hr : 0 < r) :
    x ∈ r • frontier {x : V | p x ≤ 1} ↔ p x = r := by
  rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne', hp.frontier_sublevel_eq_level hcont]
  change p (r⁻¹ • x) = 1 ↔ p x = r
  rw [hp.smul_nonneg r⁻¹ (inv_nonneg.mpr hr.le) x]
  constructor
  · intro h
    calc
      p x = r * (r⁻¹ * p x) := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
      _ = r := by rw [h, mul_one]
  · intro h
    rw [h, inv_mul_cancel₀ hr.ne']

end Geometry

section Measure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Boundary nullity from the actual homothety volume formula. In particular
no convexity, central symmetry, or sphere Lipschitz assumption is needed here. -/
theorem measure_frontier_sublevel_eq_zero (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {p : V → ℝ} (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (hS : IsCompact {x : V | p x ≤ 1}) : μ (frontier {x : V | p x ≤ 1}) = 0 := by
  let S : Set V := {x | p x ≤ 1}
  have hbdS : frontier S ⊆ S := by rw [hS.isClosed.frontier_eq]; exact diff_subset
  have hbdfin : μ (frontier S) ≠ ∞ := measure_ne_top_of_subset hbdS hS.measure_ne_top
  have hsqueeze : ∀ c ∈ Ioo (0 : ℝ) 1,
      μ.real (frontier S) ≤ (1 - c ^ Module.finrank ℝ V) * μ.real S := by
    intro c hc
    have hcontract : c • S ⊆ S :=
      (hp.contract_sublevel_subset_interior hcont hc.1.le hc.2).trans interior_subset
    calc
      μ.real (frontier S) ≤ μ.real (S \ (c • S)) :=
        measureReal_mono (hp.frontier_sublevel_subset_shell hcont hc.1.le hc.2)
          (measure_ne_top_of_subset diff_subset hS.measure_ne_top)
      _ = μ.real S - μ.real (c • S) :=
        measureReal_diff hcontract (IsCompact.smul c hS).measurableSet hS.measure_ne_top
      _ = (1 - c ^ Module.finrank ℝ V) * μ.real S := by
        rw [measureReal_smul_of_nonneg μ hc.1.le]
        ring
  have h1 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  haveI : NeBot (𝓝[Ioo (0 : ℝ) 1] (1 : ℝ)) := mem_closure_iff_nhdsWithin_neBot.mp h1
  have hlim : Tendsto (fun c : ℝ ↦ (1 - c ^ Module.finrank ℝ V) * μ.real S)
      (𝓝[Ioo (0 : ℝ) 1] (1 : ℝ)) (𝓝 0) := by
    have hfun : Continuous (fun c : ℝ ↦ (1 - c ^ Module.finrank ℝ V) * μ.real S) := by fun_prop
    have hpoint : ContinuousWithinAt
        (fun c : ℝ ↦ (1 - c ^ Module.finrank ℝ V) * μ.real S)
        (Ioo (0 : ℝ) 1) (1 : ℝ) := hfun.continuousWithinAt
    simpa only [one_pow, sub_self, zero_mul] using hpoint.tendsto
  have hle : μ.real (frontier S) ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin hsqueeze)
  apply (measureReal_eq_zero_iff hbdfin).mp
  exact le_antisymm hle measureReal_nonneg

theorem measure_smul_eq_zero_of_measure_eq_zero (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {S : Set V} (hS : μ S = 0) (r : ℝ) : μ (r • S) = 0 := by
  rw [Measure.addHaar_smul, hS, mul_zero]

variable [Nontrivial V]

omit [MeasurableSpace V] [BorelSpace V] in
theorem RadialStarBody.frontier_carrier_eq_level (K : RadialStarBody V)
    {C : ℝ≥0} (hC : LipschitzWith C K.radius) :
    frontier K.carrier = {x : V | K.gauge x = 1} := by
  obtain ⟨L, hL⟩ := K.exists_gauge_lipschitz hC
  rw [K.carrier_eq_sublevel]
  exact K.gauge_homogeneous.frontier_sublevel_eq_level hL.continuous

theorem RadialStarBody.measure_frontier_carrier_eq_zero (μ : Measure V)
    [Measure.IsAddHaarMeasure μ] (K : RadialStarBody V)
    {C : ℝ≥0} (hC : LipschitzWith C K.radius) : μ (frontier K.carrier) = 0 := by
  obtain ⟨L, hL⟩ := K.exists_gauge_lipschitz hC
  have hcompact := K.isCompact_carrier
  rw [K.carrier_eq_sublevel] at hcompact ⊢
  exact measure_frontier_sublevel_eq_zero μ K.gauge_homogeneous hL.continuous hcompact

theorem RadialStarBody.measure_scaled_frontier_eq_zero (μ : Measure V)
    [Measure.IsAddHaarMeasure μ] (K : RadialStarBody V)
    {C : ℝ≥0} (hC : LipschitzWith C K.radius) (r : ℝ) : μ (r • frontier K.carrier) = 0 :=
  measure_smul_eq_zero_of_measure_eq_zero μ (K.measure_frontier_carrier_eq_zero μ hC) r

/-- An exact-family boundary map has null image because its gauge is constant
and positive on the boundary parameter set. No measurability of the map itself
is needed for this outer-measure conclusion. -/
theorem RadialStarBody.measure_image_eq_zero_of_gauge_eq (μ : Measure V)
    [Measure.IsAddHaarMeasure μ] (K : RadialStarBody V)
    {C : ℝ≥0} (hC : LipschitzWith C K.radius) {X : Type*} (f : X → V) (D : Set X)
    {r : ℝ} (hr : 0 < r) (hlevel : ∀ x ∈ D, K.gauge (f x) = r) : μ (f '' D) = 0 := by
  obtain ⟨L, hL⟩ := K.exists_gauge_lipschitz hC
  have hsub : f '' D ⊆ r • frontier K.carrier := by
    rintro y ⟨x, hx, rfl⟩
    rw [K.carrier_eq_sublevel]
    exact (K.gauge_homogeneous.mem_pos_smul_frontier_sublevel_iff hL.continuous _ hr).mpr
      (hlevel x hx)
  exact measure_mono_null hsub (K.measure_scaled_frontier_eq_zero μ hC r)

end Measure

end BanachIsometric
