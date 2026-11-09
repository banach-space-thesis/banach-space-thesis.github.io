import BanachIsometric.HemisphereContraction

/-! The actual equator is parametrized by the literal unit sphere in the
orthogonal hyperplane, with continuous inclusions into both closed hemispheres. -/

noncomputable section

namespace BanachIsometric

open Set Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev EquatorSphere (v : sphere (0 : V) 1) := sphere (0 : (ℝ ∙ v.val)ᗮ) 1

def equatorInclusion (v : sphere (0 : V) 1) : C(EquatorSphere v, sphere (0 : V) 1) := by
  refine ⟨fun x => ⟨x.val.val, ?_⟩, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right]
    exact norm_eq_of_mem_sphere x
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val : Continuous (fun z : (ℝ ∙ v.val)ᗮ => (z : V))).comp
      (continuous_subtype_val : Continuous (fun z : EquatorSphere v => (z : (ℝ ∙ v.val)ᗮ)))

theorem equatorInclusion_inner (v : sphere (0 : V) 1) (x : EquatorSphere v) :
    inner ℝ v.val (equatorInclusion v x).val = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.val.property

def equatorNorth (v : sphere (0 : V) 1) : C(EquatorSphere v, closedHemisphere v) := by
  refine ⟨fun x => ⟨equatorInclusion v x, ?_⟩, ?_⟩
  · change 0 ≤ inner ℝ v.val (equatorInclusion v x).val
    rw [equatorInclusion_inner]
  · exact (equatorInclusion v).continuous.subtype_mk _

def equatorSouth (v : sphere (0 : V) 1) : C(EquatorSphere v, closedHemisphere (-v)) := by
  refine ⟨fun x => ⟨equatorInclusion v x, ?_⟩, ?_⟩
  · change 0 ≤ inner ℝ (-v.val) (equatorInclusion v x).val
    rw [inner_neg_left, equatorInclusion_inner, neg_zero]
  · exact (equatorInclusion v).continuous.subtype_mk _

@[simp] theorem equatorNorth_val (v : sphere (0 : V) 1) (x : EquatorSphere v) :
    (equatorNorth v x).val = equatorInclusion v x := rfl

@[simp] theorem equatorSouth_val (v : sphere (0 : V) 1) (x : EquatorSphere v) :
    (equatorSouth v x).val = equatorInclusion v x := rfl

theorem pathConnectedSpace_equator (v : sphere (0 : V) 1)
    (hrank : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ) : PathConnectedSpace (EquatorSphere v) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)

end BanachIsometric
