import BanachIsometric.FiniteNerveOpenStarCover
import BanachIsometric.UniformFinsetBarycenter
import Mathlib.Analysis.Convex.Contractible

/-! Nonempty intersections of the actual vertex stars are contractible.
The center of the contraction is the barycenter of the selected vertices. -/

noncomputable section
namespace BanachIsometric.FiniteNerve.Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ambientStarIntersection (K : Complex ι) (s : Finset ι) : Set (ι → ℝ) :=
  {w | w ∈ K.space ∧ ∀ i ∈ s, 0 < w i}

def vertexStarIntersection (K : Complex ι) (s : Finset ι) : Set K.space :=
  {w | ∀ i ∈ s, w ∈ K.vertexOpenStar i}

theorem selectedVertexBarycenter_mem_coordinateFace {s t : Finset ι}
    (hs : s.Nonempty) (hst : s ⊆ t) :
    uniformFinsetBarycenter s ∈ coordinateFace t := by
  refine ⟨uniformFinsetBarycenter_mem_stdSimplex hs, ?_⟩
  intro i hi
  have hnot : i ∉ s := fun his => hi (hst his)
  simp only [uniformFinsetBarycenter, if_neg hnot]

theorem starConvex_ambientStarIntersection (K : Complex ι) (s : Finset ι)
    (hs : s.Nonempty) :
    StarConvex ℝ (uniformFinsetBarycenter s) (K.ambientStarIntersection s) := by
  intro w hw a b ha hb hab
  obtain ⟨t, ht, hwt⟩ := (K.mem_space_iff w).mp hw.1
  have hst : s ⊆ t := by
    intro i hi
    by_contra hnot
    exact (ne_of_gt (hw.2 i hi)) (hwt.2 i hnot)
  refine ⟨(K.mem_space_iff _).mpr ⟨t, ht,
    coordinateFace_convex t (selectedVertexBarycenter_mem_coordinateFace hs hst) hwt ha hb hab⟩, ?_⟩
  intro i hi
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hcenter : 0 < uniformFinsetBarycenter s i := by
    simpa only [uniformFinsetBarycenter, if_pos hi] using inv_pos.mpr hcard
  change 0 < a * uniformFinsetBarycenter s i + b * w i
  by_cases hap : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos hap hcenter) (mul_nonneg hb (hw.2 i hi).le)
  · have hbp : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hcenter.le) (mul_pos hbp (hw.2 i hi))

def starIntersectionAmbientHomeomorph (K : Complex ι) (s : Finset ι) :
    K.vertexStarIntersection s ≃ₜ K.ambientStarIntersection s where
  toFun w := ⟨w.val.val, w.val.property, w.property⟩
  invFun w := ⟨⟨w.val, w.property.1⟩, w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem vertexStarIntersection_contractibleSpace (K : Complex ι) (s : Finset ι)
    (hs : s.Nonempty) (hne : (K.vertexStarIntersection s).Nonempty) :
    ContractibleSpace (K.vertexStarIntersection s) := by
  let e := K.starIntersectionAmbientHomeomorph s
  letI : ContractibleSpace (K.ambientStarIntersection s) :=
    (K.starConvex_ambientStarIntersection s hs).contractibleSpace
      (by obtain ⟨w, hw⟩ := hne; exact ⟨e ⟨w, hw⟩, (e ⟨w, hw⟩).property⟩)
  exact e.contractibleSpace

theorem vertexStarIntersection_eq_iInter (K : Complex ι) (s : Finset ι) :
    K.vertexStarIntersection s = ⋂ i ∈ s, K.vertexOpenStar i := by
  ext w
  simp [vertexStarIntersection]

theorem isOpen_vertexStarIntersection (K : Complex ι) (s : Finset ι) :
    IsOpen (K.vertexStarIntersection s) := by
  rw [vertexStarIntersection_eq_iInter]
  exact s.finite_toSet.isOpen_biInter (fun i _ => K.isOpen_vertexOpenStar i)

end BanachIsometric.FiniteNerve.Complex
