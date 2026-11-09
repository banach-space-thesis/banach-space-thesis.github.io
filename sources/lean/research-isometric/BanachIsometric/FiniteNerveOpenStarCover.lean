import BanachIsometric.FiniteNervePolyhedron

/-! The actual finite open cover of a coordinate polyhedron by its positive
vertex-coordinate stars. Every point is covered because its nonnegative
barycentric coordinates sum to one. -/

noncomputable section
namespace BanachIsometric.FiniteNerve.Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vertexOpenStar (K : Complex ι) (i : ι) : Set K.space := {w | 0 < w.val i}

theorem isOpen_vertexOpenStar (K : Complex ι) (i : ι) : IsOpen (K.vertexOpenStar i) :=
  isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)

theorem exists_mem_vertexOpenStar (K : Complex ι) (w : K.space) :
    ∃ i : ι, w ∈ K.vertexOpenStar i := by
  obtain ⟨s, _hs, hws⟩ := (K.mem_space_iff w.val).mp w.property
  have hsum : (0 : ℝ) < ∑ i, w.val i := by rw [hws.1.2]; exact zero_lt_one
  obtain ⟨i, _hi, hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hws.1.1 i)).mp hsum
  exact ⟨i, hpos⟩

theorem iUnion_vertexOpenStar (K : Complex ι) : (⋃ i, K.vertexOpenStar i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  obtain ⟨i, hi⟩ := K.exists_mem_vertexOpenStar w
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

end BanachIsometric.FiniteNerve.Complex
