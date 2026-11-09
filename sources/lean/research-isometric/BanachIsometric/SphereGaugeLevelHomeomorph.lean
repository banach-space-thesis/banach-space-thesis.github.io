import BanachIsometric.RadialHomeomorphism
import Mathlib.Analysis.NormedSpace.Normalize

/-! A continuous definite positive homogeneous gauge has its actual level-one
set homeomorphic to the actual auxiliary unit sphere. These are restrictions
of the already proved mutually inverse radial maps; the inverse is literal
normalization. No convexity or symmetry is required. -/

noncomputable section
namespace BanachIsometric

open NormedSpace
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : V → ℝ}

def sphereGaugeLevelHomeomorph (hp : IsDefinitePositiveHomogeneous p)
    (hcont : Continuous p) : Metric.sphere (0 : V) 1 ≃ₜ {v : V // p v = 1} where
  toFun u := ⟨radialGaugeMap p u.val, by
    rw [gauge_radialGaugeMap hp]
    exact mem_sphere_zero_iff_norm.mp u.property⟩
  invFun v := ⟨radialGaugeMapInv p v.val, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_radialGaugeMapInv hp, v.property]⟩
  left_inv u := Subtype.ext (radialGaugeMapInv_map hp u.val)
  right_inv v := Subtype.ext (radialGaugeMap_mapInv hp v.val)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (radialGaugeHomeomorph hp hcont).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_radialGaugeMapInv hp hcont).comp continuous_subtype_val

@[simp] theorem sphereGaugeLevelHomeomorph_apply_val
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (u : Metric.sphere (0 : V) 1) :
    (sphereGaugeLevelHomeomorph hp hcont u).val = radialGaugeMap p u.val := rfl

@[simp] theorem sphereGaugeLevelHomeomorph_symm_apply_val
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (v : {v : V // p v = 1}) :
    ((sphereGaugeLevelHomeomorph hp hcont).symm v).val = normalize v.val := by
  change radialGaugeMapInv p v.val = normalize v.val
  rw [radialGaugeMapInv, v.property, one_div, NormedSpace.normalize]

end BanachIsometric
