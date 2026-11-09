import BanachIsometric.SphereSimplyConnected
import BanachIsometric.HomogeneousGeometry

/-! Actual compact closed hemispheres and their explicit normalized affine
contractions from the pole. -/

noncomputable section

namespace BanachIsometric

open Set Metric NormedSpace
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def closedHemisphere (v : sphere (0 : V) 1) : Set (sphere (0 : V) 1) :=
  {x | 0 ≤ inner ℝ v.val x.val}

theorem isCompact_closedHemisphere [FiniteDimensional ℝ V] (v : sphere (0 : V) 1) :
    IsCompact (closedHemisphere v) := by
  letI : CompactSpace (sphere (0 : V) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  exact (isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)).isCompact

theorem hemisphere_interpolation_ne_zero (v : sphere (0 : V) 1)
    (x : closedHemisphere v) (t : unitInterval) :
    (1 - (t : ℝ)) • v.val + (t : ℝ) • x.val.val ≠ 0 := by
  intro hz
  have hv : ‖v.val‖ = 1 := norm_eq_of_mem_sphere v
  have hx : ‖x.val.val‖ = 1 := norm_eq_of_mem_sphere x.val
  have hvv : inner ℝ v.val v.val = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hi : (1 - (t : ℝ)) + (t : ℝ) * inner ℝ v.val x.val.val = 0 := by
    have he := congrArg (fun z : V => inner ℝ v.val z) hz
    simpa only [inner_add_right, inner_smul_right, hvv, mul_one, inner_zero_right] using he
  have hpos : 0 ≤ (t : ℝ) * inner ℝ v.val x.val.val := mul_nonneg t.property.1 x.property
  have ht : (t : ℝ) = 1 := by linarith [t.property.2]
  rw [ht, sub_self, zero_smul, one_smul, zero_add] at hz
  rw [hz, norm_zero] at hx
  norm_num at hx

def hemisphereContraction (v : sphere (0 : V) 1) :
    C(unitInterval × closedHemisphere v, sphere (0 : V) 1) := by
  let f : unitInterval × closedHemisphere v → V := fun z =>
    (1 - (z.1 : ℝ)) • v.val + (z.1 : ℝ) • z.2.val.val
  have hf : Continuous f := by
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
  have hne : ∀ z, f z ≠ 0 := fun z => hemisphere_interpolation_ne_zero v z.2 z.1
  refine ⟨fun z => ⟨normalize (f z), ?_⟩, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using norm_normalize (hne z)
  · apply Continuous.subtype_mk
    exact (hf.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (hne z))).smul hf

@[simp] theorem hemisphereContraction_zero (v : sphere (0 : V) 1) (x : closedHemisphere v) :
    hemisphereContraction v (0, x) = v := by
  apply Subtype.ext
  change normalize ((1 - (0 : ℝ)) • v.val + (0 : ℝ) • x.val.val) = v.val
  simp only [sub_zero, one_smul, zero_smul, add_zero]
  exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere v)

@[simp] theorem hemisphereContraction_one (v : sphere (0 : V) 1) (x : closedHemisphere v) :
    hemisphereContraction v (1, x) = x.val := by
  apply Subtype.ext
  change normalize ((1 - (1 : ℝ)) • v.val + (1 : ℝ) • x.val.val) = x.val.val
  simp only [sub_self, zero_smul, one_smul, zero_add]
  exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x.val)

end BanachIsometric
