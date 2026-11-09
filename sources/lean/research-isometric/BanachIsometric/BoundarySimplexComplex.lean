import BanachIsometric.FiniteNervePolyhedron
import BanachIsometric.SimplexBoundarySphereHomeomorph

/-! The boundary of the ACTUAL standard simplex is realized by the finite
complex of nonempty proper vertex subsets. Its geometric realization is
homeomorphic to the genuine Euclidean sphere using the previously proved
explicit radial formula. No simplicial/singular comparison is assumed. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open SphereGenerator

def boundarySimplexComplex (n : ℕ) : FiniteNerve.Complex (Fin (n + 3)) where
  faces := Finset.univ.filter (fun s => s.Nonempty ∧ s ≠ Finset.univ)
  nonempty s hs := (Finset.mem_filter.mp hs).2.1
  downward s hs t hts ht := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ?_⟩
    intro htu
    have hsu : s = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      exact hts (htu ▸ Finset.mem_univ i)
    exact (Finset.mem_filter.mp hs).2.2 hsu

theorem mem_boundarySimplexComplex_space (n : ℕ) (w : Fin (n + 3) → ℝ) :
    w ∈ (boundarySimplexComplex n).space ↔
      w ∈ stdSimplex ℝ (Fin (n + 3)) ∧ ∃ i, w i = 0 := by
  constructor
  · intro hw
    obtain ⟨s, hs, hws⟩ := (boundarySimplexComplex n).mem_space_iff w |>.mp hw
    have hsu : s ≠ Finset.univ := (Finset.mem_filter.mp hs).2.2
    have hex : ∃ i, i ∉ s := by
      by_contra h
      apply hsu
      exact Finset.eq_univ_of_forall (by simpa using h)
    obtain ⟨i, hi⟩ := hex
    exact ⟨hws.1, i, hws.2 i hi⟩
  · rintro ⟨hw, i, hi⟩
    apply (boundarySimplexComplex n).mem_space_iff w |>.mpr
    refine ⟨Finset.univ.erase i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Finset.univ_nontrivial.erase_nonempty, ?_⟩, hw, ?_⟩
    · intro h
      have hm : i ∈ Finset.univ.erase i := h.symm ▸ Finset.mem_univ i
      exact Finset.notMem_erase i Finset.univ hm
    · intro j hj
      have hji : j = i := by simpa using hj
      simpa [hji] using hi

def boundarySimplexRealizationHomeomorph (n : ℕ) :
    (boundarySimplexComplex n).space ≃ₜ SimplexBoundary n where
  toFun w := ⟨⟨w.val, ((mem_boundarySimplexComplex_space n w.val).mp w.property).1⟩,
    ((mem_boundarySimplexComplex_space n w.val).mp w.property).2⟩
  invFun w := ⟨w.val.val, (mem_boundarySimplexComplex_space n w.val.val).mpr
    ⟨w.val.property, w.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

def boundarySimplexComplexSphereHomeomorph (n : ℕ) :
    (boundarySimplexComplex n).space ≃ₜ Sph (n + 1) :=
  (boundarySimplexRealizationHomeomorph n).trans (simplexBoundarySphereHomeomorph n)

end BanachIsometric.SingularPrism
