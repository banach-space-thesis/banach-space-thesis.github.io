import BanachIsometric.ConvexSingularAcyclicity
import BanachIsometric.ContractibleZeroHomology

/-! Actual finite closed stars and their affine contraction. A closed star is
the downward closure of the faces containing its apex. Its full realization
need not be convex, but is proved star convex and hence contractible. The
positive singular homology vanishing and H0 identification use the already
proved actual prism homotopy, rather than an acyclicity premise. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coordinateFace_mono {s t : Finset ι} (hst : s ⊆ t) :
    coordinateFace s ⊆ coordinateFace t := by
  intro w hw
  exact ⟨hw.1, fun i hi => hw.2 i (fun his => hi (hst his))⟩

theorem vertex_mem_coordinateFace {s : Finset ι} {i : ι} (hi : i ∈ s) :
    vertex i ∈ coordinateFace s := by
  refine ⟨single_mem_stdSimplex ℝ i, ?_⟩
  intro j hj
  have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
  simp [vertex, hji]

namespace Complex

def closedStar (K : Complex ι) (i : ι) : Complex ι where
  faces := K.faces.filter (fun s => ∃ t ∈ K.faces, i ∈ t ∧ s ⊆ t)
  nonempty := fun s hs => K.nonempty s (Finset.mem_filter.mp hs).1
  downward := by
    intro s hs u hus hu
    obtain ⟨hsK, t, htK, hit, hst⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨K.downward s hsK u hus hu, t, htK, hit, hus.trans hst⟩

theorem mem_closedStar_faces_iff (K : Complex ι) (i : ι) (s : Finset ι) :
    s ∈ (K.closedStar i).faces ↔ s ∈ K.faces ∧ ∃ t ∈ K.faces, i ∈ t ∧ s ⊆ t := by
  simp only [closedStar, Finset.mem_filter]

theorem insert_mem_closedStar_faces (K : Complex ι) (i : ι) (s : Finset ι)
    (hs : s ∈ (K.closedStar i).faces) : insert i s ∈ (K.closedStar i).faces := by
  obtain ⟨_hsK, t, htK, hit, hst⟩ := (K.mem_closedStar_faces_iff i s).mp hs
  have hist : insert i s ⊆ t := Finset.insert_subset hit hst
  exact (K.mem_closedStar_faces_iff i _).mpr
    ⟨K.downward t htK _ hist (Finset.insert_nonempty _ _), t, htK, hit, hist⟩

theorem mem_closedStar_space_iff (K : Complex ι) (i : ι) (w : ι → ℝ) :
    w ∈ (K.closedStar i).space ↔
      ∃ t ∈ K.faces, i ∈ t ∧ w ∈ coordinateFace t := by
  constructor
  · intro hw
    obtain ⟨s, hs, hws⟩ := (mem_space_iff _ _).mp hw
    obtain ⟨_hsK, t, htK, hit, hst⟩ := (K.mem_closedStar_faces_iff i s).mp hs
    exact ⟨t, htK, hit, coordinateFace_mono hst hws⟩
  · rintro ⟨t, htK, hit, hwt⟩
    exact (mem_space_iff _ _).mpr
      ⟨t, (K.mem_closedStar_faces_iff i t).mpr ⟨htK, t, htK, hit, Finset.Subset.refl _⟩, hwt⟩

theorem starConvex_closedStar (K : Complex ι) (i : ι) :
    StarConvex ℝ (vertex i) (K.closedStar i).space := by
  intro w hw a b ha hb hab
  obtain ⟨t, htK, hit, hwt⟩ := (K.mem_closedStar_space_iff i w).mp hw
  exact (K.mem_closedStar_space_iff i _).mpr
    ⟨t, htK, hit, coordinateFace_convex t (vertex_mem_coordinateFace hit) hwt ha hb hab⟩

theorem closedStar_contractibleSpace (K : Complex ι) (i : ι)
    (hi : ∃ t ∈ K.faces, i ∈ t) : ContractibleSpace (K.closedStar i).space := by
  apply (K.starConvex_closedStar i).contractibleSpace
  obtain ⟨t, htK, hit⟩ := hi
  exact ⟨vertex i, (K.mem_closedStar_space_iff i _).mpr
    ⟨t, htK, hit, vertex_mem_coordinateFace hit⟩⟩

theorem closedStar_rawPositiveHomology_subsingleton (K : Complex ι) (i : ι)
    (hi : ∃ t ∈ K.faces, i ∈ t) (n : ℕ) :
    Subsingleton (SingularPrism.RawPositiveHomology (K.closedStar i).space n) := by
  letI := K.closedStar_contractibleSpace i hi
  exact SingularPrism.rawPositiveHomology_contractible _ n

def closedStar_rawZeroHomologyEquiv (K : Complex ι) (i : ι)
    (hi : ∃ t ∈ K.faces, i ∈ t) :
    SingularPrism.RawZeroHomology (K.closedStar i).space ≃ₗ[ℚ] ℚ := by
  letI := K.closedStar_contractibleSpace i hi
  exact SingularPrism.rawZeroHomologyContractibleEquiv _

end Complex
end BanachIsometric.FiniteNerve
