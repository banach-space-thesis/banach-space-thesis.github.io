import BanachIsometric.FiniteNervePolyhedron

/-! Literal standard-simplex maps into the actual finite nerve polyhedron.
The maps are barycentric coordinate aggregation and commute with every
vertex map, including face inclusions and degeneracies. This geometric
construction is independent of any homology comparison theorem. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open Set Finset

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

theorem stdSimplex_map_mem_coordinateFace (v : α → ι) (t : stdSimplex ℝ α) :
    (stdSimplex.map v t).val ∈ coordinateFace (Finset.univ.image v) := by
  refine ⟨(stdSimplex.map v t).property, ?_⟩
  intro i hi
  have hne (j : α) : v j ≠ i := by
    intro he
    exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he⟩)
  change FunOnFinite.linearMap ℝ ℝ v t.val i = 0
  simp [FunOnFinite.linearMap_apply_apply, hne]

def faceBarycentricMap (K : Complex ι) (v : α → ι) (hv : Finset.univ.image v ∈ K.faces) :
    C(stdSimplex ℝ α, K.space) where
  toFun t := ⟨(stdSimplex.map v t).val,
    (K.mem_space_iff _).mpr ⟨Finset.univ.image v, hv, stdSimplex_map_mem_coordinateFace v t⟩⟩
  continuous_toFun :=
    (continuous_subtype_val.comp (stdSimplex.continuous_map v)).subtype_mk _

theorem face_of_vertexMap (K : Complex ι) (f : α → β) (v : β → ι)
    (hv : Finset.univ.image v ∈ K.faces) [Nonempty α] :
    Finset.univ.image (v ∘ f) ∈ K.faces := by
  apply K.downward _ hv _
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨f j, Finset.mem_univ _, rfl⟩
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem faceBarycentricMap_naturality (K : Complex ι) (f : α → β) (v : β → ι)
    (hv : Finset.univ.image v ∈ K.faces) [Nonempty α] (t : stdSimplex ℝ α) :
    faceBarycentricMap K (v ∘ f) (face_of_vertexMap K f v hv) t =
      faceBarycentricMap K v hv (stdSimplex.map f t) := by
  apply Subtype.ext
  change (stdSimplex.map (v ∘ f) t).val = (stdSimplex.map v (stdSimplex.map f t)).val
  exact congrArg (fun w : stdSimplex ℝ ι => w.val) (stdSimplex.map_comp_apply f v t).symm

theorem faceBarycentricMap_vertex [DecidableEq α] (K : Complex ι) (v : α → ι)
    (hv : Finset.univ.image v ∈ K.faces) (i : α) :
    (faceBarycentricMap K v hv (stdSimplex.vertex i) : ι → ℝ) = vertex (v i) := by
  exact congrArg Subtype.val (stdSimplex.map_vertex v i)

end BanachIsometric.FiniteNerve

