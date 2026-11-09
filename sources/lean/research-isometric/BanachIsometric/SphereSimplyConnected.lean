import BanachIsometric.TwoOpenVanKampen
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.NormedSpace.Connected

/-!
# Simple connectivity of actual finite-dimensional spheres

Two stereographic charts are contractible, and their overlap is the image of
a punctured real hyperplane. The proved two-open van Kampen theorem supplies
simple connectivity. No sphere fundamental-group premise is used.
-/

noncomputable section

namespace BanachIsometric

open Set Metric Module
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sphereComplementHomeomorph (v : sphere (0 : E) 1) :
    (ℝ ∙ v.val)ᗮ ≃ₜ ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere v)).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_stereographic_symm (norm_eq_of_mem_sphere v) v.property))

theorem isSimplyConnected_sphere_complement (v : sphere (0 : E) 1) :
    TwoOpenCover.IsSimplyConnected ({v}ᶜ : Set (sphere (0 : E) 1)) := by
  let e := sphereComplementHomeomorph v
  letI : ContractibleSpace ({v}ᶜ : Set (sphere (0 : E) 1)) :=
    e.contractibleSpace_iff.mp inferInstance
  change SimplyConnectedSpace ({v}ᶜ : Set (sphere (0 : E) 1))
  infer_instance

theorem sphere_ne_neg (v : sphere (0 : E) 1) : v ≠ -v := by
  intro he
  have hval : v.val = -v.val := congrArg Subtype.val he
  have hz : (2 : ℝ) • v.val = 0 := by
    calc (2 : ℝ) • v.val = v.val + v.val := two_smul ℝ v.val
      _ = -v.val + v.val := congrArg (fun z => z + v.val) hval
      _ = 0 := neg_add_cancel v.val
  have hv0 : v.val = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have hv := norm_eq_of_mem_sphere v
  rw [hv0, norm_zero] at hv
  norm_num at hv

/-- Stereographic coordinates identify the overlap of the antipodal charts
with the punctured orthogonal hyperplane. -/
theorem stereographic_image_compl_zero (v : sphere (0 : E) 1) :
    (stereographic (norm_eq_of_mem_sphere v)).symm '' ({0}ᶜ : Set (ℝ ∙ v.val)ᗮ) =
      ({v}ᶜ ∩ {-v}ᶜ : Set (sphere (0 : E) 1)) := by
  let f := (stereographic (norm_eq_of_mem_sphere v)).symm
  have hinj : Function.Injective f :=
    (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere v)).injective
  have hmem : -v ∈ (stereographic (norm_eq_of_mem_sphere v)).source := by
    simp only [stereographic_source, mem_compl_iff, mem_singleton_iff]
    exact (sphere_ne_neg v).symm
  have hzero : f 0 = -v := by
    have h := (stereographic (norm_eq_of_mem_sphere v)).left_inv hmem
    rw [stereographic_apply_neg] at h
    exact h
  rw [Set.image_compl_eq_range_diff_image hinj, Set.image_singleton]
  change Set.range f \ {f 0} = _
  rw [hzero]
  change Set.range (stereographic (norm_eq_of_mem_sphere v)).symm \ {-v} = _
  rw [range_stereographic_symm (norm_eq_of_mem_sphere v) v.property]
  rfl

/-- The unit sphere is simply connected whenever the orthogonal hyperplane
to a unit vector has real dimension greater than one. -/
theorem simplyConnectedSpace_sphere_of_orthogonal_rank
    [FiniteDimensional ℝ E]
    (v : sphere (0 : E) 1) (hE : 1 < Module.rank ℝ E)
    (hH : 1 < Module.rank ℝ (ℝ ∙ v.val)ᗮ) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  letI : PathConnectedSpace (sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hE 0 zero_le_one)
  apply TwoOpenCover.simplyConnectedSpace_of_two_open
    (U := {v}ᶜ) (V := {-v}ᶜ) isOpen_compl_singleton isOpen_compl_singleton
  · ext x
    simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_cases hx : x = v
    · subst x
      exact Or.inr (sphere_ne_neg v)
    · exact Or.inl hx
  · exact isSimplyConnected_sphere_complement v
  · exact isSimplyConnected_sphere_complement (-v)
  · rw [← stereographic_image_compl_zero v]
    exact (isPathConnected_compl_singleton_of_one_lt_rank hH 0).image
      (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere v)).continuous

/-- The actual metric `n`-sphere is simply connected for every `n ≥ 2`. -/
theorem simplyConnectedSpace_euclidean_sphere (n : ℕ) (hn : 2 ≤ n) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let v : sphere (0 : E) 1 := ⟨EuclideanSpace.single (0 : Fin (n + 1)) 1, by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_single]
    norm_num⟩
  have hv0 : v.val ≠ 0 := by
    intro hz
    have hv := norm_eq_of_mem_sphere v
    rw [hz, norm_zero] at hv
    norm_num at hv
  letI : Fact (finrank ℝ E = n + 1) := ⟨by simp [E]⟩
  have hHdim : finrank ℝ (ℝ ∙ v.val)ᗮ = n :=
    Submodule.finrank_orthogonal_span_singleton hv0
  apply simplyConnectedSpace_sphere_of_orthogonal_rank v
  · rw [← Module.finrank_eq_rank, show finrank ℝ E = n + 1 by simp [E]]
    exact_mod_cast (show 1 < n + 1 by omega)
  · rw [← Module.finrank_eq_rank, hHdim]
    exact_mod_cast (show 1 < n by omega)

end BanachIsometric
