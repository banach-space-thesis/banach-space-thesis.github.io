import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Tactic

/-! Finite abstract complexes realized by literal standard coordinate simplices.
This is a genuine finite polyhedron, with its inherited Euclidean topology;
no homological or finite-CW conclusion is part of its definition. -/

noncomputable section
namespace BanachIsometric.FiniteNerve

open Set Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vertex (i : ι) : ι → ℝ := Pi.single i 1

omit [Fintype ι] in
theorem vertex_injective : Function.Injective (vertex : ι → (ι → ℝ)) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij i
  simp [vertex, hne] at h

def coordinateFace (s : Finset ι) : Set (ι → ℝ) :=
  {w | w ∈ stdSimplex ℝ ι ∧ ∀ i ∉ s, w i = 0}

omit [DecidableEq ι] in
theorem coordinateFace_convex (s : Finset ι) : Convex ℝ (coordinateFace s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_stdSimplex ℝ ι hx.1 hy.1 ha hb hab, ?_⟩
  intro i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx.2 i hi, hy.2 i hi,
    mul_zero, add_zero]

theorem coordinateFace_eq_convexHull (s : Finset ι) :
    coordinateFace s = convexHull ℝ (vertex '' (s : Set ι)) := by
  apply Set.Subset.antisymm
  · intro w hw
    have hsum : ∑ i ∈ s, w i = 1 := by
      calc
        ∑ i ∈ s, w i = ∑ i, w i :=
          Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hw.2 i hi)
        _ = 1 := hw.1.2
    have heq : ∑ i ∈ s, w i • vertex i = w := by
      ext i
      by_cases hi : i ∈ s
      · simp [vertex, Finset.sum_apply, Pi.single_apply, hi]
      · simp [vertex, Finset.sum_apply, Pi.single_apply, hi, hw.2 i hi]
    rw [← heq, ← s.centerMass_eq_of_sum_1 vertex hsum]
    exact s.centerMass_mem_convexHull (fun i _ => hw.1.1 i)
      (hsum.symm ▸ zero_lt_one) (fun i hi => mem_image_of_mem vertex hi)
  · apply convexHull_min
    · rintro _ ⟨i, hi, rfl⟩
      refine ⟨single_mem_stdSimplex ℝ i, ?_⟩
      intro j hj
      have hne : j ≠ i := fun hji => hj (hji.symm ▸ hi)
      simp [vertex, hne.symm]
    · exact coordinateFace_convex s

theorem coordinateFace_inter (s t : Finset ι) :
    coordinateFace s ∩ coordinateFace t = coordinateFace (s ∩ t) := by
  ext w
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨hs.1, ?_⟩
    intro i hi
    by_cases his : i ∈ s
    · exact ht.2 i (fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩))
    · exact hs.2 i his
  · intro h
    exact ⟨⟨h.1, fun i hi => h.2 i (fun hit => hi (Finset.mem_inter.mp hit).1)⟩,
      ⟨h.1, fun i hi => h.2 i (fun hit => hi (Finset.mem_inter.mp hit).2)⟩⟩

omit [DecidableEq ι] in
theorem coordinateFace_compact (s : Finset ι) : IsCompact (coordinateFace s) := by
  have hc : IsClosed {w : ι → ℝ | ∀ i ∉ s, w i = 0} :=
    by
      convert isClosed_iInter (fun i => isClosed_iInter (fun _ : i ∉ s =>
        isClosed_eq (continuous_apply i) (continuous_const : Continuous (fun _ : (ι → ℝ) => (0 : ℝ))))) using 1
      ext w
      simp
  exact (isCompact_stdSimplex ι).inter_right hc

omit [Fintype ι] in
theorem vertex_affineIndependent : AffineIndependent ℝ (vertex : ι → (ι → ℝ)) := by
  intro s w hw hz i hi
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hz
  have h := congrFun hz i
  simpa [vertex, Finset.sum_apply, Pi.single_apply, hi] using h

/-- An actual finite abstract simplicial complex, excluding the empty face. -/
structure Complex (ι : Type*) [Fintype ι] [DecidableEq ι] where
  faces : Finset (Finset ι)
  nonempty : ∀ s ∈ faces, s.Nonempty
  downward : ∀ s ∈ faces, ∀ t ⊆ s, t.Nonempty → t ∈ faces

namespace Complex

def space (K : Complex ι) : Set (ι → ℝ) :=
  ⋃ s ∈ K.faces, coordinateFace s

theorem mem_space_iff (K : Complex ι) (w : ι → ℝ) :
    w ∈ K.space ↔ ∃ s ∈ K.faces, w ∈ coordinateFace s := by simp [space]

theorem isCompact_space (K : Complex ι) : IsCompact K.space :=
  K.faces.isCompact_biUnion fun s _ => coordinateFace_compact s

theorem space_eq_finite_union_convexHulls (K : Complex ι) :
    K.space = ⋃ s ∈ K.faces, convexHull ℝ (vertex '' (s : Set ι)) := by
  simp only [space, coordinateFace_eq_convexHull]

def geometricVertices (s : Finset ι) : Finset (ι → ℝ) := s.image vertex

def toSimplicialComplex (K : Complex ι) : Geometry.SimplicialComplex ℝ (ι → ℝ) where
  faces := {t | ∃ s ∈ K.faces, t = geometricVertices s}
  empty_notMem := by
    rintro ⟨s, hs, he⟩
    obtain ⟨i, hi⟩ := K.nonempty s hs
    have hv : vertex i ∈ geometricVertices s := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [← he] at hv
    exact Finset.notMem_empty _ hv
  indep := by
    rintro t ⟨s, _hs, rfl⟩
    apply vertex_affineIndependent.range.mono
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact mem_range_self i
  down_closed := by
    rintro s t ⟨a, ha, rfl⟩ hts ht
    let b := a.filter (fun i => vertex i ∈ t)
    have hbt : geometricVertices b = t := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hi).2
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hx)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩
    have hb : b.Nonempty := by
      by_contra h
      have hb0 : b = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      apply ht
      rw [← hbt, hb0]
      rfl
    exact ⟨b, K.downward a ha b (Finset.filter_subset _ _) hb, hbt.symm⟩
  inter_subset_convexHull := by
    rintro s t ⟨a, _ha, rfl⟩ ⟨b, _hb, rfl⟩
    let all : Finset (ι → ℝ) := Finset.univ.image vertex
    have hAll : AffineIndependent ℝ ((↑) : all → (ι → ℝ)) := by
      apply vertex_affineIndependent.range.mono
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact mem_range_self i
    have hsub (s : Finset ι) : geometricVertices s ⊆ all :=
      Finset.image_subset_image (Finset.subset_univ s)
    exact (hAll.convexHull_inter (hsub a) (hsub b)).symm.subset

theorem toSimplicialComplex_space (K : Complex ι) : K.toSimplicialComplex.space = K.space := by
  ext w
  simp only [Geometry.SimplicialComplex.mem_space_iff, toSimplicialComplex, Set.mem_setOf_eq,
    mem_space_iff]
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, hw⟩
    refine ⟨s, hs, ?_⟩
    rw [coordinateFace_eq_convexHull]
    simpa only [geometricVertices, Finset.coe_image] using hw
  · rintro ⟨s, hs, hw⟩
    refine ⟨geometricVertices s, ⟨s, hs, rfl⟩, ?_⟩
    rw [coordinateFace_eq_convexHull] at hw
    simpa only [geometricVertices, Finset.coe_image] using hw

theorem toSimplicialComplex_faces_finite (K : Complex ι) :
    K.toSimplicialComplex.faces.Finite := by
  have he : K.toSimplicialComplex.faces =
      (K.faces.image geometricVertices : Set (Finset (ι → ℝ))) := by
    ext t
    simp only [toSimplicialComplex, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image]
    exact ⟨fun ⟨s, hs, he⟩ => ⟨s, hs, he.symm⟩,
      fun ⟨s, hs, he⟩ => ⟨s, hs, he.symm⟩⟩
  rw [he]
  exact Finset.finite_toSet _

end Complex
end BanachIsometric.FiniteNerve
