import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Radial description of homogeneous sublevel sets

These are the elementary radial identities used in Sections 2 and 5 of
Acuaviva--Kania. Convexity, central symmetry, and the triangle inequality for
the function are not assumed. The norm is only an auxiliary coordinate norm.
-/

namespace BanachIsometric

open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Definite nonnegative functions homogeneous only for nonnegative real scalars.
Evenness is deliberately not part of this definition. -/
structure IsDefinitePositiveHomogeneous (p : V → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  eq_zero_iff : ∀ x, p x = 0 ↔ x = 0
  smul_nonneg : ∀ (t : ℝ), 0 ≤ t → ∀ x, p (t • x) = t * p x

/-- The positive radial function of the sublevel set of a definite gauge. -/
noncomputable def reciprocalRadial (p : V → ℝ) (u : V) : ℝ := (p u)⁻¹

theorem IsDefinitePositiveHomogeneous.pos {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {x : V} (hx : x ≠ 0) : 0 < p x := by
  have hne : p x ≠ 0 := fun h => hx ((hp.eq_zero_iff x).mp h)
  exact lt_of_le_of_ne (hp.nonneg x) (Ne.symm hne)

/-- Recover the gauge from its restriction to the auxiliary unit sphere. -/
theorem IsDefinitePositiveHomogeneous.radial_identity {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {x : V} (hx : x ≠ 0) :
    p x = ‖x‖ * p (‖x‖⁻¹ • x) := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simpa only [smul_smul, mul_inv_cancel₀ hnorm, one_smul] using
    hp.smul_nonneg ‖x‖ (norm_nonneg x) (‖x‖⁻¹ • x)

theorem IsDefinitePositiveHomogeneous.reciprocalRadial_pos {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {u : V} (hu : ‖u‖ = 1) :
    0 < reciprocalRadial p u := by
  apply inv_pos.mpr
  apply hp.pos
  intro h
  simp [h] at hu

/-- The intersection of the gauge's unit sublevel set with each nonnegative
unit ray is the interval from zero to the reciprocal radial value. -/
theorem IsDefinitePositiveHomogeneous.smul_mem_sublevel_iff {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {u : V} (hu : ‖u‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    p (t • u) ≤ 1 ↔ t ≤ reciprocalRadial p u := by
  have hpu : 0 < p u := hp.pos (by intro h; simp [h] at hu)
  rw [hp.smul_nonneg t ht u, reciprocalRadial]
  exact (le_div_iff₀ hpu).symm.trans (by simp [one_div])

/-- The full radial parametrisation, with the origin included explicitly so
the result also applies to the zero-dimensional auxiliary space. -/
theorem IsDefinitePositiveHomogeneous.sublevel_eq_radial {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) :
    {x : V | p x ≤ 1} =
      {x : V | x = 0 ∨ ∃ (u : V) (t : ℝ), ‖u‖ = 1 ∧ 0 ≤ t ∧
        t ≤ reciprocalRadial p u ∧ x = t • u} := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hnorm]
      have hreconstruct : x = ‖x‖ • (‖x‖⁻¹ • x) := by
        rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
      refine Or.inr ⟨‖x‖⁻¹ • x, ‖x‖, hu, norm_nonneg x, ?_, hreconstruct⟩
      apply (hp.smul_mem_sublevel_iff hu (norm_nonneg x)).mp
      rwa [← hreconstruct]
  · rintro (rfl | ⟨u, t, hu, ht, hr, rfl⟩)
    · simp [(hp.eq_zero_iff 0).mpr rfl]
    · exact (hp.smul_mem_sublevel_iff hu ht).mpr hr

omit [NormedSpace ℝ V] in
/-- A lower bound away from zero turns a Lipschitz gauge into a Lipschitz
reciprocal radial function. This applies on a sphere without convexity. -/
theorem reciprocalRadial_lipschitzOnWith {p : V → ℝ} {s : Set V}
    {C ε : ℝ≥0} (hε : 0 < ε) (hp : LipschitzOnWith C p s)
    (hlower : ∀ x ∈ s, (ε : ℝ) ≤ p x) :
    LipschitzOnWith (C / ε ^ 2) (reciprocalRadial p) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hεr : 0 < (ε : ℝ) := hε
  have hpx : 0 < p x := hεr.trans_le (hlower x hx)
  have hpy : 0 < p y := hεr.trans_le (hlower y hy)
  have hprod : (ε : ℝ) ^ 2 ≤ p x * p y := by
    nlinarith [hlower x hx, hlower y hy]
  have hdenom : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos hεr
  calc
    dist (reciprocalRadial p x) (reciprocalRadial p y) =
        dist (p x) (p y) / (p x * p y) := by
      rw [reciprocalRadial, reciprocalRadial,
        dist_inv_inv₀ (ne_of_gt hpx) (ne_of_gt hpy),
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpx, abs_of_pos hpy]
    _ ≤ dist (p x) (p y) / (ε : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left dist_nonneg hdenom hprod
    _ ≤ ((C : ℝ) * dist x y) / (ε : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right (hp.dist_le_mul x hx y hy) hdenom.le
    _ = ((C / ε ^ 2 : ℝ≥0) : ℝ) * dist x y := by
      push_cast
      ring

omit [NormedSpace ℝ V] in
/-- Continuity of the radial function follows from the same quantitative bound. -/
theorem reciprocalRadial_continuousOn {p : V → ℝ} {s : Set V}
    {C ε : ℝ≥0} (hε : 0 < ε) (hp : LipschitzOnWith C p s)
    (hlower : ∀ x ∈ s, (ε : ℝ) ≤ p x) :
    ContinuousOn (reciprocalRadial p) s :=
  (reciprocalRadial_lipschitzOnWith hε hp hlower).continuousOn

end BanachIsometric
