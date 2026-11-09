import BanachIsometric.BoundarySimplexComplex
import BanachIsometric.FiniteNerveOrderedFaces

/-! Literal ordered facets of the finite boundary simplex. The facets are
distinct, and there is no full-dimensional simplex in this complex. These
are finite combinatorial facts, not a singular-homology comparison. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve

theorem boundarySimplexFacet_image_mem (n : ℕ) (i : Fin (n + 3)) :
    Finset.univ.image i.succAbove ∈ (boundarySimplexComplex n).faces := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Finset.image_nonempty.mpr Finset.univ_nonempty, ?_⟩
  intro h
  have hi : i ∈ Finset.univ.image i.succAbove := h.symm ▸ Finset.mem_univ i
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  exact Fin.succAbove_ne i j hj

def boundarySimplexFacet (n : ℕ) (i : Fin (n + 3)) :
    StrictOrderedSimplex (boundarySimplexComplex n) (n + 1) :=
  ⟨⟨(Fin.succAboveOrderEmb i).toOrderHom, boundarySimplexFacet_image_mem n i⟩,
    Fin.strictMono_succAbove i⟩

@[simp] theorem boundarySimplexFacet_apply (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (boundarySimplexFacet n i).val.val j = i.succAbove j := rfl

theorem boundarySimplexFacet_injective (n : ℕ) : Function.Injective (boundarySimplexFacet n) := by
  intro i j h
  apply Fin.succAbove_left_injective
  funext k
  exact congrArg (fun v : StrictOrderedSimplex (boundarySimplexComplex n) (n + 1) =>
    v.val.val k) h

theorem boundarySimplex_no_full_simplex (n : ℕ) :
    IsEmpty (StrictOrderedSimplex (boundarySimplexComplex n) (n + 2)) := by
  refine ⟨fun v => ?_⟩
  have hsur : Function.Surjective v.val.val :=
    Finite.surjective_of_injective v.property.injective
  have himage : Finset.univ.image v.val.val = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨j, rfl⟩ := hsur i
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  exact (Finset.mem_filter.mp v.val.property).2.2 himage

end BanachIsometric.SingularPrism
