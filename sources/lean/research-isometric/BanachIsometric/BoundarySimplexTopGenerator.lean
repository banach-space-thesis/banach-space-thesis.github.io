import BanachIsometric.FullSimplexComplex
import BanachIsometric.BoundarySimplexTopCycle
import BanachIsometric.FiniteNerveLeastVertexConeIdentity

/-! The explicit top class GENERATES the actual finite boundary-simplex
homology. A cycle is included in the full simplex and filled by the proved
least-vertex cone operator. The full simplex's top chain space has exactly
one basis simplex. Its boundary is the literal alternating facet cycle.
No comparison with singular homology is used. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve Module

theorem fullSimplexTop_boundary (n : ℕ) :
    finiteRationalBoundary (fullSimplexComplex n) (n + 1)
      (Finsupp.single (fullSimplexTopSimplex n) 1) =
    finiteComplexChainInclusion (boundarySimplex_faces_subset_full n) (n + 1)
      (boundarySimplexTopCycle n).val := by
  change _ = finiteComplexChainInclusion (boundarySimplex_faces_subset_full n) (n + 1)
    ((rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr (boundarySimplexTopChain n))
  rw [finiteRationalBoundary_single]
  simp only [boundarySimplexTopChain, map_sum, map_zsmul, Basis.repr_self,
    finiteComplexChainInclusion_single, fullSimplexTop_face]

theorem boundarySimplexTopCycle_spans (n : ℕ)
    (x : rationalCycles (boundarySimplexComplex n) (n + 1)) :
    ∃ a : ℚ, x = a • boundarySimplexTopCycle n := by
  let hinc := boundarySimplex_faces_subset_full n
  have hx : finiteRationalBoundary (boundarySimplexComplex n) n x.val = 0 := x.property
  have hxc : finiteRationalBoundary (fullSimplexComplex n) n
      (finiteComplexChainInclusion hinc (n + 1) x.val) = 0 := by
    calc
      _ = finiteComplexChainInclusion hinc n
          (finiteRationalBoundary (boundarySimplexComplex n) n x.val) :=
        LinearMap.congr_fun (finiteComplexChainInclusion_boundary hinc n) x.val
      _ = 0 := by rw [hx, map_zero]
  obtain ⟨y, hy⟩ := exists_boundary_of_cycle_leastVertexCone (fullSimplexComplex n)
    (fullSimplex_closed_under_bottom n) n
    (finiteComplexChainInclusion hinc (n + 1) x.val) hxc
  rw [fullSimplexTopChain_single n y, map_smul, fullSimplexTop_boundary, ← map_smul] at hy
  have hc := finiteComplexChainInclusion_injective hinc (n + 1) hy
  refine ⟨y (fullSimplexTopSimplex n), ?_⟩
  apply Subtype.ext
  exact hc.symm

theorem boundarySimplexTopClass_spans (n : ℕ)
    (q : QuotientRationalHomology (boundarySimplexComplex n) (n + 1)) :
    ∃ a : ℚ, q = a • boundarySimplexTopClass n := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨a, ha⟩ := boundarySimplexTopCycle_spans n x
    refine ⟨a, ?_⟩
    change Submodule.Quotient.mk x = a • Submodule.Quotient.mk (boundarySimplexTopCycle n)
    rw [ha, Submodule.Quotient.mk_smul]

def boundarySimplexTopHomologyEquiv (n : ℕ) :
    ℚ ≃ₗ[ℚ] QuotientRationalHomology (boundarySimplexComplex n) (n + 1) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℚ _ (boundarySimplexTopClass n))
    ⟨LinearMap.ker_eq_bot.mp
        (LinearMap.ker_toSpanSingleton ℚ _ (boundarySimplexTopClass_ne_zero n)),
      fun q => by
        obtain ⟨a, ha⟩ := boundarySimplexTopClass_spans n q
        exact ⟨a, ha.symm⟩⟩

@[simp] theorem boundarySimplexTopHomologyEquiv_one (n : ℕ) :
    boundarySimplexTopHomologyEquiv n 1 = boundarySimplexTopClass n := by
  change (1 : ℚ) • boundarySimplexTopClass n = boundarySimplexTopClass n
  exact one_smul _ _

end BanachIsometric.SingularPrism
