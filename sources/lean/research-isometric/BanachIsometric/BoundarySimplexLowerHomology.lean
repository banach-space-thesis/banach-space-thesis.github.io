import BanachIsometric.BoundarySimplexLowerChains
import BanachIsometric.FiniteNerveLeastVertexConeIdentity

/-! The actual finite boundary simplex has zero positive homology below its
top dimension. The filler is obtained from the explicit full-simplex cone;
in these dimensions that filler is still a literal boundary-simplex chain.
No singular comparison or homological vanishing premise is used. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve

theorem boundarySimplex_lower_cycle_fills (n d : ℕ) (hd : d < n)
    (x : FiniteRationalChains (boundarySimplexComplex n) (d + 1))
    (hx : finiteRationalBoundary (boundarySimplexComplex n) d x = 0) :
    ∃ y : FiniteRationalChains (boundarySimplexComplex n) (d + 2),
      finiteRationalBoundary (boundarySimplexComplex n) (d + 1) y = x := by
  let hinc := boundarySimplex_faces_subset_full n
  have hxc : finiteRationalBoundary (fullSimplexComplex n) d
      (finiteComplexChainInclusion hinc (d + 1) x) = 0 := by
    calc
      _ = finiteComplexChainInclusion hinc d
          (finiteRationalBoundary (boundarySimplexComplex n) d x) :=
        LinearMap.congr_fun (finiteComplexChainInclusion_boundary hinc d) x
      _ = 0 := by rw [hx, map_zero]
  obtain ⟨z, hz⟩ := exists_boundary_of_cycle_leastVertexCone (fullSimplexComplex n)
    (fullSimplex_closed_under_bottom n) d
    (finiteComplexChainInclusion hinc (d + 1) x) hxc
  let e := boundarySimplexLowerChainEquiv n (d + 2) (by omega)
  let y := e.symm z
  have hy : finiteComplexChainInclusion hinc (d + 2) y = z := by
    have he := boundarySimplexLowerChainEquiv_eq_inclusion n (d + 2) (by omega)
    rw [← he]
    exact e.apply_symm_apply z
  refine ⟨y, ?_⟩
  apply finiteComplexChainInclusion_injective hinc (d + 1)
  calc
    _ = finiteRationalBoundary (fullSimplexComplex n) (d + 1)
        (finiteComplexChainInclusion hinc (d + 2) y) :=
      (LinearMap.congr_fun (finiteComplexChainInclusion_boundary hinc (d + 1)) y).symm
    _ = finiteRationalBoundary (fullSimplexComplex n) (d + 1) z := by rw [hy]
    _ = _ := hz

theorem boundarySimplex_lower_homology_subsingleton (n d : ℕ) (hd : d < n) :
    Subsingleton (QuotientRationalHomology (boundarySimplexComplex n) (d + 1)) := by
  apply (Submodule.Quotient.subsingleton_iff _).mpr
  intro x
  have hx : finiteRationalBoundary (boundarySimplexComplex n) d x.val = 0 := x.property
  obtain ⟨y, hy⟩ := boundarySimplex_lower_cycle_fills n d hd x.val hx
  exact ⟨y, Subtype.ext hy⟩

end BanachIsometric.SingularPrism
