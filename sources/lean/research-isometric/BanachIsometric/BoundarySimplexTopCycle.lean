import BanachIsometric.BoundarySimplexFacets
import BanachIsometric.FiniteNerveRawSingularMap
import BanachIsometric.FiniteNerveRationalQuotientHomology
import BanachIsometric.AlternatingFaceCycle

/-!
# The nonzero top class of the actual finite boundary simplex

The explicit alternating facet sum is a cycle in the actual finite ordered
chain complex. It is nonzero, and there are no chains in the next dimension,
so its class in the literal cycles/boundaries quotient is nonzero.
This is FINITE simplicial homology; no injection into singular homology is
inferred from degreewise chain injectivity.
-/

noncomputable section
namespace BanachIsometric.SingularPrism

open FiniteNerve Module

def boundarySimplexTopChain (n : ℕ) : RationalChains (boundarySimplexComplex n) (n + 1) :=
  ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
    rationalChainBasis (boundarySimplexComplex n) (n + 1) (boundarySimplexFacet n i)

theorem boundarySimplexFacet_barycentric_face (n : ℕ) (i j : Fin (n + 2)) (h : i ≤ j) :
    (barycentricSingularSimplex (boundarySimplexComplex n) (n + 1)
      (boundarySimplexFacet n j.succ)).comp (face i) =
    (barycentricSingularSimplex (boundarySimplexComplex n) (n + 1)
      (boundarySimplexFacet n i.castSucc)).comp (face j) := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  change (face j.succ (face i w)).val = (face i.castSucc (face j w)).val
  exact congrArg Subtype.val (ContinuousMap.congr_fun (face_face i j h) w)

theorem boundarySimplexTopChain_boundary (n : ℕ) :
    rationalBoundary (boundarySimplexComplex n) n (boundarySimplexTopChain n) = 0 := by
  apply rationalToRawSingularChain_injective (boundarySimplexComplex n) n
  rw [map_zero]
  have he := LinearMap.congr_fun
    (rationalToRawSingularChain_boundary (boundarySimplexComplex n) n)
    (boundarySimplexTopChain n)
  change rawBoundary n (rationalToRawSingularChain (boundarySimplexComplex n) (n + 1)
    (boundarySimplexTopChain n)) = rationalToRawSingularChain (boundarySimplexComplex n) n
      (rationalBoundary (boundarySimplexComplex n) n (boundarySimplexTopChain n)) at he
  rw [← he]
  simp only [boundarySimplexTopChain, map_sum, map_zsmul,
    rationalToRawSingularChain_basis]
  simpa only [map_sum, map_zsmul] using rawBoundary_alternating_face_family n
    (fun i => barycentricSingularSimplex (boundarySimplexComplex n) (n + 1)
      (boundarySimplexFacet n i)) (boundarySimplexFacet_barycentric_face n)

theorem boundarySimplexTopChain_coefficient (n : ℕ) :
    ((rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr
      (boundarySimplexTopChain n)) (boundarySimplexFacet n 0) = 1 := by
  classical
  simp [boundarySimplexTopChain, Finset.sum_apply, Finsupp.single_apply,
    (boundarySimplexFacet_injective n).eq_iff]

theorem boundarySimplexTopChain_ne_zero (n : ℕ) : boundarySimplexTopChain n ≠ 0 := by
  intro h
  have hc := boundarySimplexTopChain_coefficient n
  rw [h, map_zero, Finsupp.zero_apply] at hc
  norm_num at hc

theorem boundarySimplex_next_chains_subsingleton (n : ℕ) :
    Subsingleton (FiniteRationalChains (boundarySimplexComplex n) (n + 2)) := by
  letI := boundarySimplex_no_full_simplex n
  infer_instance

def boundarySimplexTopCycle (n : ℕ) : rationalCycles (boundarySimplexComplex n) (n + 1) :=
  ⟨(rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr (boundarySimplexTopChain n), by
    change finiteRationalBoundary (boundarySimplexComplex n) n
      ((rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr
        (boundarySimplexTopChain n)) = 0
    rw [finiteRationalBoundary_repr, boundarySimplexTopChain_boundary, map_zero]⟩

def boundarySimplexTopClass (n : ℕ) :
    QuotientRationalHomology (boundarySimplexComplex n) (n + 1) :=
  Submodule.Quotient.mk (boundarySimplexTopCycle n)

theorem boundarySimplexTopClass_ne_zero (n : ℕ) : boundarySimplexTopClass n ≠ 0 := by
  intro h
  have hm : boundarySimplexTopCycle n ∈ rationalBoundaries (boundarySimplexComplex n) (n + 1) :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  obtain ⟨b, hb⟩ := hm
  haveI := boundarySimplex_next_chains_subsingleton n
  have hb0 : b = 0 := Subsingleton.elim _ _
  rw [hb0, map_zero] at hb
  have hc : (rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr
      (boundarySimplexTopChain n) = 0 := by
    exact (congrArg Subtype.val hb).symm
  apply boundarySimplexTopChain_ne_zero n
  apply (rationalChainBasis (boundarySimplexComplex n) (n + 1)).repr.injective
  rw [hc, map_zero]

end BanachIsometric.SingularPrism
