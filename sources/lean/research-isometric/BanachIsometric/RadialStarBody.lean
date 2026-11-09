import BanachIsometric.StarBodyCompact
import Mathlib.Analysis.Convex.Gauge

/-!
# Star bodies from positive continuous radial functions

This is the paper's actual radial-set description, with no convexity or
central symmetry. The auxiliary space is nontrivial, as it is in the paper's
geometric theorems (their ambient real dimension is at least four).
-/

namespace BanachIsometric

open NormedSpace Set
open scoped NNReal Pointwise

/-- A star body about zero, specified by its strictly positive continuous
radius on the auxiliary unit sphere. -/
structure RadialStarBody (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Nontrivial V] where
  radius : Metric.sphere (0 : V) 1 → ℝ
  radius_pos : ∀ u, 0 < radius u
  radius_continuous : Continuous radius

namespace RadialStarBody

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]

/-- The normalized direction, as an actual unit-sphere point. -/
noncomputable def unitDirection (x : V) (hx : x ≠ 0) : Metric.sphere (0 : V) 1 :=
  ⟨normalize x, by simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize hx⟩

omit [NormedSpace ℝ V] [Nontrivial V] in
theorem unit_norm (u : Metric.sphere (0 : V) 1) : ‖u.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

omit [NormedSpace ℝ V] [Nontrivial V] in
theorem unit_ne_zero (u : Metric.sphere (0 : V) 1) : u.val ≠ 0 := by
  intro hu
  have hh := unit_norm u
  simp [hu] at hh

omit [Nontrivial V] in
theorem unitDirection_unit (u : Metric.sphere (0 : V) 1) :
    unitDirection u.val (unit_ne_zero u) = u := by
  apply Subtype.ext
  exact normalize_eq_self_of_norm_eq_one (unit_norm u)

/-- The carrier is exactly the union of the radial intervals in equation (1)
of the paper; the origin is not inserted by a separate union. -/
def carrier (K : RadialStarBody V) : Set V :=
  {x | ∃ (u : Metric.sphere (0 : V) 1) (t : ℝ),
    0 ≤ t ∧ t ≤ K.radius u ∧ x = t • u.val}

/-- The radial gauge, with its value at zero specified separately. -/
noncomputable def gauge (K : RadialStarBody V) (x : V) : ℝ := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ / K.radius (unitDirection x hx)

@[simp] theorem gauge_zero (K : RadialStarBody V) : K.gauge 0 = 0 := by simp [gauge]

theorem gauge_of_ne (K : RadialStarBody V) (x : V) (hx : x ≠ 0) :
    K.gauge x = ‖x‖ / K.radius (unitDirection x hx) := by simp [gauge, hx]

theorem gauge_pos (K : RadialStarBody V) {x : V} (hx : x ≠ 0) : 0 < K.gauge x := by
  rw [K.gauge_of_ne x hx]
  exact div_pos (norm_pos_iff.mpr hx) (K.radius_pos _)

theorem gauge_unit (K : RadialStarBody V) (u : Metric.sphere (0 : V) 1) :
    K.gauge u.val = (K.radius u)⁻¹ := by
  rw [K.gauge_of_ne u.val (unit_ne_zero u), unitDirection_unit, unit_norm, one_div]

theorem gauge_smul_nonneg (K : RadialStarBody V) (t : ℝ) (ht : 0 ≤ t) (x : V) :
    K.gauge (t • x) = t * K.gauge x := by
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases hx : x = 0
  · simp [hx]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have htx : t • x ≠ 0 := smul_ne_zero ht0 hx
  have hdir : unitDirection (t • x) htx = unitDirection x hx := by
    apply Subtype.ext
    exact normalize_smul_of_pos htp x
  rw [K.gauge_of_ne (t • x) htx, K.gauge_of_ne x hx, hdir,
    norm_smul, Real.norm_of_nonneg ht]
  ring

theorem gauge_homogeneous (K : RadialStarBody V) : IsDefinitePositiveHomogeneous K.gauge where
  nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    exact (K.gauge_pos hx).le
  eq_zero_iff x := by
    constructor
    · intro hp
      by_contra hx
      exact (ne_of_gt (K.gauge_pos hx)) hp
    · rintro rfl
      exact K.gauge_zero
  smul_nonneg := K.gauge_smul_nonneg

theorem zero_mem_carrier (K : RadialStarBody V) : (0 : V) ∈ K.carrier := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨unitDirection v hv, 0, le_rfl, (K.radius_pos _).le, by simp⟩

theorem carrier_eq_sublevel (K : RadialStarBody V) : K.carrier = {x : V | K.gauge x ≤ 1} := by
  ext x
  constructor
  · rintro ⟨u, t, ht, hr, rfl⟩
    change K.gauge (t • u.val) ≤ 1
    rw [K.gauge_smul_nonneg t ht, K.gauge_unit]
    exact (mul_inv_le_iff₀ (K.radius_pos u)).mpr (by simpa only [one_mul] using hr)
  · intro hx
    change K.gauge x ≤ 1 at hx
    by_cases hx0 : x = 0
    · simpa only [hx0] using K.zero_mem_carrier
    refine ⟨unitDirection x hx0, ‖x‖, norm_nonneg x, ?_, ?_⟩
    · rw [K.gauge_of_ne x hx0] at hx
      exact (div_le_one (K.radius_pos _)).mp hx
    · exact (norm_smul_normalize x).symm

theorem mem_pos_smul_carrier_iff (K : RadialStarBody V) (x : V) {r : ℝ} (hr : 0 < r) :
    x ∈ r • K.carrier ↔ K.gauge x ≤ r := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hr), K.carrier_eq_sublevel]
  change K.gauge (r⁻¹ • x) ≤ 1 ↔ K.gauge x ≤ r
  rw [K.gauge_smul_nonneg r⁻¹ (inv_nonneg.mpr hr.le) x]
  simpa only [div_eq_mul_inv, mul_comm] using
    (div_le_one hr : K.gauge x / r ≤ 1 ↔ K.gauge x ≤ r)

/-- The explicit radial formula is exactly Mathlib's infimum-defined
Minkowski functional of this carrier. No convexity assumption enters. -/
theorem gauge_eq_minkowski (K : RadialStarBody V) (x : V) :
    _root_.gauge K.carrier x = K.gauge x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hset : {r : ℝ | 0 < r ∧ x ∈ r • K.carrier} = Ici (K.gauge x) := by
    ext r
    constructor
    · rintro ⟨hr, hmem⟩
      exact (K.mem_pos_smul_carrier_iff x hr).mp hmem
    · intro hr
      have hrpos : 0 < r := (K.gauge_pos hx).trans_le hr
      exact ⟨hrpos, (K.mem_pos_smul_carrier_iff x hrpos).mpr hr⟩
  change sInf {r : ℝ | 0 < r ∧ x ∈ r • K.carrier} = K.gauge x
  rw [hset, csInf_Ici]

theorem gauge_continuousOn_sphere (K : RadialStarBody V) :
    ContinuousOn K.gauge (Metric.sphere 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun u : Metric.sphere (0 : V) 1 => K.gauge u.val)
  have hh : Continuous (fun u : Metric.sphere (0 : V) 1 => (K.radius u)⁻¹) :=
    K.radius_continuous.inv₀ (fun u => ne_of_gt (K.radius_pos u))
  simpa only [gauge_unit] using hh

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- Positive inner and finite outer radii follow from the radial assumptions;
they are not extra axioms of the body. -/
theorem radius_bounds (K : RadialStarBody V) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ u, ε ≤ K.radius u ∧ K.radius u ≤ M := by
  letI : CompactSpace (Metric.sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  have hc : IsCompact (Set.univ : Set (Metric.sphere (0 : V) 1)) := isCompact_univ
  obtain ⟨ε, hε, hlower⟩ := hc.exists_forall_le'
    K.radius_continuous.continuousOn (a := 0) (fun u _ => K.radius_pos u)
  obtain ⟨B, hB⟩ := hc.bddAbove_image K.radius_continuous.continuousOn
  refine ⟨ε, max 1 B, hε, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u
  exact ⟨hlower u (mem_univ _), (hB (mem_image_of_mem K.radius (mem_univ u))).trans
    (le_max_right _ _)⟩

theorem isCompact_carrier (K : RadialStarBody V) : IsCompact K.carrier := by
  letI : CompactSpace (Metric.sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  obtain ⟨_, M, _, _, hbounds⟩ := K.radius_bounds
  let D : Set ((Metric.sphere (0 : V) 1) × ℝ) :=
    {z | 0 ≤ z.2 ∧ z.2 ≤ K.radius z.1}
  have hDclosed : IsClosed D :=
    (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd (K.radius_continuous.comp continuous_fst))
  have hDcompact : IsCompact D :=
    (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) M))).of_isClosed_subset
      hDclosed (fun z hz => ⟨mem_univ _, hz.1, hz.2.trans (hbounds z.1).2⟩)
  have hmap : Continuous (fun z : (Metric.sphere (0 : V) 1) × ℝ => z.2 • z.1.val) :=
    continuous_snd.smul (continuous_subtype_val.comp continuous_fst)
  have himage : (fun z : (Metric.sphere (0 : V) 1) × ℝ => z.2 • z.1.val) '' D = K.carrier := by
    ext x
    constructor
    · rintro ⟨⟨u, t⟩, ht, rfl⟩
      exact ⟨u, t, ht.1, ht.2, rfl⟩
    · rintro ⟨u, t, ht, hr, rfl⟩
      exact ⟨(u, t), ⟨ht, hr⟩, rfl⟩
  rw [← himage]
  exact hDcompact.image hmap

theorem contains_closedBall (K : RadialStarBody V) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : V) r ⊆ K.carrier := by
  rw [K.carrier_eq_sublevel]
  exact K.gauge_homogeneous.contains_closedBall K.gauge_continuousOn_sphere

theorem zero_mem_interior (K : RadialStarBody V) : (0 : V) ∈ interior K.carrier := by
  rw [K.carrier_eq_sublevel]
  exact K.gauge_homogeneous.zero_mem_interior_sublevel K.gauge_continuousOn_sphere

/-- Inverting the positive radial function preserves Lipschitz regularity,
with a uniform lower bound supplied by compactness of the sphere. -/
theorem exists_inverse_radius_lipschitz (K : RadialStarBody V) {C : ℝ≥0}
    (hC : LipschitzWith C K.radius) :
    ∃ D : ℝ≥0, LipschitzWith D (fun u => (K.radius u)⁻¹) := by
  obtain ⟨ε, _, hε, _, hbounds⟩ := K.radius_bounds
  let εn : ℝ≥0 := ⟨ε, hε.le⟩
  refine ⟨C / εn ^ 2, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  have hprod : ε ^ 2 ≤ K.radius u * K.radius v := by
    nlinarith [(hbounds u).1, (hbounds v).1]
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  calc
    dist ((K.radius u)⁻¹) ((K.radius v)⁻¹) =
        dist (K.radius u) (K.radius v) / (K.radius u * K.radius v) := by
      rw [dist_inv_inv₀ (ne_of_gt (K.radius_pos u)) (ne_of_gt (K.radius_pos v)),
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (K.radius_pos u),
        abs_of_pos (K.radius_pos v)]
    _ ≤ dist (K.radius u) (K.radius v) / ε ^ 2 :=
      div_le_div_of_nonneg_left dist_nonneg hεsq hprod
    _ ≤ ((C : ℝ) * dist u v) / ε ^ 2 :=
      div_le_div_of_nonneg_right (hC.dist_le_mul u v) hεsq.le
    _ = ((C / εn ^ 2 : ℝ≥0) : ℝ) * dist u v := by
      push_cast
      dsimp [εn]
      ring

theorem exists_gauge_sphere_lipschitz (K : RadialStarBody V) {C : ℝ≥0}
    (hC : LipschitzWith C K.radius) :
    ∃ D : ℝ≥0, LipschitzOnWith D K.gauge (Metric.sphere 0 1) := by
  obtain ⟨D, hD⟩ := K.exists_inverse_radius_lipschitz hC
  refine ⟨D, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  have hh := hD.dist_le_mul (⟨u, hu⟩ : Metric.sphere (0 : V) 1) ⟨v, hv⟩
  simpa only [← K.gauge_unit] using hh

/-- The global estimate applies to nonconvex, asymmetric star bodies: neither
convexity nor central symmetry is used in deriving Lipschitz regularity. -/
theorem exists_gauge_lipschitz (K : RadialStarBody V) {C : ℝ≥0}
    (hC : LipschitzWith C K.radius) : ∃ L : ℝ≥0, LipschitzWith L K.gauge := by
  obtain ⟨D, hD⟩ := K.exists_gauge_sphere_lipschitz hC
  exact K.gauge_homogeneous.exists_lipschitzWith hD

end FiniteDimensional

/-- Conversely, a definite homogeneous gauge continuous on the auxiliary
sphere produces its positive radial star body. -/
noncomputable def ofGauge (p : V → ℝ) (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) : RadialStarBody V where
  radius u := (p u.val)⁻¹
  radius_pos u := inv_pos.mpr (hp.pos (unit_ne_zero u))
  radius_continuous := by
    have hh : Continuous (fun u : Metric.sphere (0 : V) 1 => p u.val) :=
      continuousOn_iff_continuous_restrict.mp hcont
    exact hh.inv₀ (fun u => ne_of_gt (hp.pos (unit_ne_zero u)))

@[simp] theorem ofGauge_radius (p : V → ℝ) (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) (u : Metric.sphere (0 : V) 1) :
    (ofGauge p hp hcont).radius u = (p u.val)⁻¹ := rfl

/-- The radial reconstruction recovers exactly the original gauge, rather
than an equivalent function or norm. -/
@[simp] theorem ofGauge_gauge (p : V → ℝ) (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) (x : V) :
    (ofGauge p hp hcont).gauge x = p x := by
  by_cases hx : x = 0
  · simp [hx, (hp.eq_zero_iff 0).mpr rfl]
  rw [(ofGauge p hp hcont).gauge_of_ne x hx]
  change ‖x‖ / (p (normalize x))⁻¹ = p x
  rw [div_inv_eq_mul]
  exact (hp.radial_identity hx).symm

theorem ofGauge_carrier (p : V → ℝ) (hp : IsDefinitePositiveHomogeneous p)
    (hcont : ContinuousOn p (Metric.sphere 0 1)) :
    (ofGauge p hp hcont).carrier = {x : V | p x ≤ 1} := by
  rw [(ofGauge p hp hcont).carrier_eq_sublevel]
  ext x
  simp only [Set.mem_setOf_eq, ofGauge_gauge]

@[ext] theorem ext {K L : RadialStarBody V} (h : K.radius = L.radius) : K = L := by
  cases K
  cases L
  cases h
  rfl

/-- Passing from a radial body to its gauge and back preserves the exact
radial function and therefore the body itself. -/
theorem ofGauge_gauge_eq (K : RadialStarBody V) :
    ofGauge K.gauge K.gauge_homogeneous K.gauge_continuousOn_sphere = K := by
  apply ext
  funext u
  simp only [ofGauge_radius, K.gauge_unit, inv_inv]

end RadialStarBody
end BanachIsometric
