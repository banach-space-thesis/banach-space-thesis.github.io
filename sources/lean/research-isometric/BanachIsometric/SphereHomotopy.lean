import BanachIsometric.HomogeneousGeometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Homotopy.Basic

/-!
# The actual sphere homotopy in the exact-family argument

Pointwise orthogonal unit-vector fields are joined inside the unit sphere.
We normalise the straight-line interpolation instead of using the paper's
trigonometric interpolation. Orthogonality proves that the interpolated vector
never vanishes. The output is an actual `ContinuousMap.Homotopy`; no degree or
homotopy-invariance assertion is assumed here.
-/

namespace BanachIsometric

open NormedSpace
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The affine combination of orthogonal unit vectors is never zero, even
when its real parameter is outside the unit interval. -/
theorem orthogonal_unit_interpolation_ne_zero {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0) (t : ℝ) :
    (1 - t) • x + t • y ≠ 0 := by
  intro hz
  have hxx : inner ℝ x x = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have ht : 1 - t = 0 := by
    have h := congrArg (fun z : V => inner ℝ x z) hz
    simpa only [inner_add_right, inner_smul_right, hxx, hxy, mul_one, mul_zero,
      add_zero, inner_zero_right] using h
  have ht1 : t = 1 := by linarith
  rw [ht1, sub_self, zero_smul, one_smul, zero_add] at hz
  have : ‖y‖ = 0 := by rw [hz, norm_zero]
  linarith

variable {X : Type*} [TopologicalSpace X]

/-- Exact homotopy of continuous sphere maps whose values are orthogonal.
The domain is arbitrary; in Theorem 3.1 it is the parameter sphere. -/
noncomputable def orthogonalSphereHomotopy
    (f g : C(X, Metric.sphere (0 : V) 1))
    (hfg : ∀ z, inner ℝ (f z).val (g z).val = 0) :
    ContinuousMap.Homotopy f g := by
  let v : unitInterval × X → V := fun p =>
    (1 - (p.1 : ℝ)) • (f p.2).val + (p.1 : ℝ) • (g p.2).val
  have hnorm (u : Metric.sphere (0 : V) 1) : ‖u.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have hv : ∀ p, v p ≠ 0 := fun p =>
    orthogonal_unit_interpolation_ne_zero (hnorm _) (hnorm _) (hfg p.2) p.1
  have hvCont : Continuous v := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (f.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (g.continuous.comp continuous_snd)))
  refine
    { toFun := fun p => ⟨normalize (v p), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize (hv p)
  · apply Continuous.subtype_mk
    exact (hvCont.norm.inv₀ (fun p => norm_ne_zero_iff.mpr (hv p))).smul hvCont
  · intro z
    apply Subtype.ext
    change normalize (v (0, z)) = (f z).val
    change normalize ((1 - (0 : ℝ)) • (f z).val + (0 : ℝ) • (g z).val) = _
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact normalize_eq_self_of_norm_eq_one (hnorm _)
  · intro z
    apply Subtype.ext
    change normalize (v (1, z)) = (g z).val
    change normalize ((1 - (1 : ℝ)) • (f z).val + (1 : ℝ) • (g z).val) = _
    simp only [sub_self, zero_smul, one_smul, zero_add]
    exact normalize_eq_self_of_norm_eq_one (hnorm _)

theorem orthogonal_sphere_maps_homotopic
    (f g : C(X, Metric.sphere (0 : V) 1))
    (hfg : ∀ z, inner ℝ (f z).val (g z).val = 0) :
    ContinuousMap.Homotopic f g :=
  ⟨orthogonalSphereHomotopy f g hfg⟩

end BanachIsometric
