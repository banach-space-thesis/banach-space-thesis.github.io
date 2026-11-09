import BanachIsometric.SphereHomotopy
import Mathlib.Analysis.Normed.Group.BallSphere

/-! A sphere map which misses one point has an explicit null-homotopy.
The homotopy normalizes the straight segment from the antipode of that point.
This supplies the orbit-evaluation step of the real even-dimensional argument. -/

namespace BanachIsometric

open NormedSpace Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem avoided_unit_interpolation_ne_zero {x p : V}
    (hx : ‖x‖ = 1) (hp : ‖p‖ = 1) (hne : x ≠ p) (t : unitInterval) :
    (1 - (t : ℝ)) • (-p) + (t : ℝ) • x ≠ 0 := by
  intro hz
  have heq : (1 - (t : ℝ)) • p = (t : ℝ) • x := by
    apply Eq.symm
    apply eq_of_sub_eq_zero
    simpa only [sub_eq_add_neg, smul_neg, add_comm] using hz
  have hnorm := congrArg norm heq
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.property.2),
    Real.norm_of_nonneg t.property.1, hp, hx, mul_one, mul_one] at hnorm
  have h₁ : (2 : ℝ) * (1 - (t : ℝ)) = 1 := by linarith
  have h₂ : (2 : ℝ) * (t : ℝ) = 1 := by linarith
  have hpq := congrArg (fun z : V => (2 : ℝ) • z) heq
  change (2 : ℝ) • ((1 - (t : ℝ)) • p) = (2 : ℝ) • ((t : ℝ) • x) at hpq
  rw [smul_smul, smul_smul, h₁, h₂, one_smul, one_smul] at hpq
  exact hne hpq.symm

noncomputable def sphereAvoidedPointHomotopy
    {X : Type*} [TopologicalSpace X]
    (f : C(X, sphere (0 : V) 1)) (p : sphere (0 : V) 1)
    (havoid : ∀ x, f x ≠ p) :
    ContinuousMap.Homotopy (ContinuousMap.const X (-p)) f := by
  let v : unitInterval × X → V := fun q =>
    (1 - (q.1 : ℝ)) • (-p.val) + (q.1 : ℝ) • (f q.2).val
  have hnorm (u : sphere (0 : V) 1) : ‖u.val‖ = 1 :=
    norm_eq_of_mem_sphere u
  have hv : ∀ q, v q ≠ 0 := by
    intro q
    apply avoided_unit_interpolation_ne_zero (hnorm _) (hnorm _)
    intro heq
    exact havoid q.2 (Subtype.ext heq)
  have hvCont : Continuous v := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      continuous_const).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (f.continuous.comp continuous_snd)))
  refine
    { toFun := fun q => ⟨normalize (v q), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · simpa only [mem_sphere, dist_zero_right] using norm_normalize (hv q)
  · apply Continuous.subtype_mk
    exact (hvCont.norm.inv₀ (fun q => norm_ne_zero_iff.mpr (hv q))).smul hvCont
  · intro x
    apply Subtype.ext
    change normalize ((1 - (0 : ℝ)) • (-p.val) + (0 : ℝ) • (f x).val) = -p.val
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact normalize_eq_self_of_norm_eq_one (by rw [norm_neg, hnorm p])
  · intro x
    apply Subtype.ext
    change normalize ((1 - (1 : ℝ)) • (-p.val) + (1 : ℝ) • (f x).val) = (f x).val
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact normalize_eq_self_of_norm_eq_one (hnorm _)

theorem sphere_map_nullhomotopic_of_avoided_point
    {X : Type*} [TopologicalSpace X]
    (f : C(X, sphere (0 : V) 1)) (p : sphere (0 : V) 1)
    (havoid : ∀ x, f x ≠ p) :
    ContinuousMap.Homotopic (ContinuousMap.const X (-p)) f :=
  ⟨sphereAvoidedPointHomotopy f p havoid⟩

end BanachIsometric
