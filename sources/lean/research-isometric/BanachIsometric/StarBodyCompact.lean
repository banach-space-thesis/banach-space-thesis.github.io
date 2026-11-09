import BanachIsometric.HomogeneousGeometry
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Compact star bodies obtained from homogeneous functions

The sphere regularity and definiteness hypotheses supply both finite outer and
positive inner radii. They are proved here, not assumed as additional geometric
hypotheses. No convexity or symmetry is used.
-/

namespace BanachIsometric

open Set
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section FiniteDimension

variable [FiniteDimensional ℝ V]

theorem IsDefinitePositiveHomogeneous.exists_sphere_bounds {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ u : V, ‖u‖ = 1 → ε ≤ p u ∧ p u ≤ M := by
  have hcompact : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere _ _
  obtain ⟨ε, hε, hlower⟩ := hcompact.exists_forall_le' hcont (a := 0) (by
    intro u hu
    apply hp.pos
    intro heq
    subst u
    simp at hu)
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hcont
  refine ⟨ε, max 1 B, hε, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  have hus : u ∈ Metric.sphere (0 : V) 1 := by simpa using hu
  exact ⟨hlower u hus, (hB (mem_image_of_mem p hus)).trans (le_max_right _ _)⟩

theorem IsDefinitePositiveHomogeneous.exists_norm_comparison {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ x : V, ε * ‖x‖ ≤ p x ∧ p x ≤ M * ‖x‖ := by
  obtain ⟨ε, M, hε, hM, hbounds⟩ := hp.exists_sphere_bounds hcont
  exact ⟨ε, M, hε, hM, fun x ↦
    ⟨hp.norm_mul_le (fun u hu ↦ (hbounds u hu).1) x,
      hp.le_norm_mul (fun u hu ↦ (hbounds u hu).2) x⟩⟩

theorem IsDefinitePositiveHomogeneous.exists_lipschitzWith {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere 0 1)) :
    ∃ L : ℝ≥0, LipschitzWith L p := by
  obtain ⟨_, M, _, hM, hbounds⟩ := hp.exists_sphere_bounds hC.continuousOn
  exact ⟨⟨M, hM.le⟩ + 2 * C,
    hp.lipschitzWith_of_sphere (M := ⟨M, hM.le⟩) (fun u hu ↦ (hbounds u hu).2) hC⟩

theorem IsDefinitePositiveHomogeneous.isCompact_sublevel {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hC : LipschitzOnWith C p (Metric.sphere 0 1)) :
    IsCompact {x : V | p x ≤ 1} := by
  obtain ⟨L, hL⟩ := hp.exists_lipschitzWith hC
  obtain ⟨ε, _, hε, _, hbounds⟩ := hp.exists_norm_comparison hC.continuousOn
  apply (isCompact_closedBall (0 : V) (1 / ε)).of_isClosed_subset
    (isClosed_le hL.continuous continuous_const)
  intro x hx
  change p x ≤ 1 at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (le_div_iff₀ hε).mpr
  nlinarith [(hbounds x).1]

theorem IsDefinitePositiveHomogeneous.contains_closedBall {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : V) r ⊆ {x : V | p x ≤ 1} := by
  obtain ⟨_, M, _, hM, hbounds⟩ := hp.exists_norm_comparison hcont
  refine ⟨1 / M, one_div_pos.mpr hM, ?_⟩
  intro x hx
  change p x ≤ 1
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hx' := (le_div_iff₀ hM).mp hx
  exact (hbounds x).2.trans (by nlinarith)

theorem IsDefinitePositiveHomogeneous.zero_mem_interior_sublevel {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) :
    (0 : V) ∈ interior {x : V | p x ≤ 1} := by
  obtain ⟨r, hr, hball⟩ := hp.contains_closedBall hcont
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : V) hr)
      (Metric.ball_subset_closedBall.trans hball))

end FiniteDimension

/-- Every boundary point of a homogeneous unit sublevel is approached from its
strict sublevel by contractions. This is the regular-closedness used to identify
a star body from its uniform measure's support. -/
theorem IsDefinitePositiveHomogeneous.sublevel_subset_closure_strict {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) :
    {x : V | p x ≤ 1} ⊆ closure {x : V | p x < 1} := by
  intro x hx
  have h1 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  have hmap : x ∈ closure ((fun t : ℝ ↦ t • x) '' Ioo (0 : ℝ) 1) := by
    simpa only [one_smul] using
      image_closure_subset_closure_image
        (continuous_id.smul continuous_const : Continuous (fun t : ℝ ↦ t • x))
        (mem_image_of_mem (fun t : ℝ ↦ t • x) h1)
  apply (closure_mono (show ((fun t : ℝ ↦ t • x) '' Ioo (0 : ℝ) 1) ⊆
      {x : V | p x < 1} from ?_)) hmap
  rintro _ ⟨t, ht, rfl⟩
  change p (t • x) < 1
  rw [hp.smul_nonneg t ht.1.le]
  change p x ≤ 1 at hx
  exact lt_of_le_of_lt (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hx ht.1.le) ht.2

theorem IsDefinitePositiveHomogeneous.sublevel_eq_closure_interior {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p) :
    {x : V | p x ≤ 1} = closure (interior {x : V | p x ≤ 1}) := by
  apply le_antisymm
  · have hO : IsOpen {x : V | p x < 1} := isOpen_lt hcont continuous_const
    have hle : {x : V | p x < 1} ⊆ {x : V | p x ≤ 1} := by
      intro x hx
      change p x < 1 at hx
      change p x ≤ 1
      exact hx.le
    have hOsub : {x : V | p x < 1} ⊆ interior {x : V | p x ≤ 1} :=
      hO.subset_interior_iff.mpr hle
    exact hp.sublevel_subset_closure_strict.trans (closure_mono hOsub)
  · exact closure_minimal interior_subset (isClosed_le hcont continuous_const)

end BanachIsometric
