import ThesisCommon.Analysis.BanachLattice

/-! Acuaviva, Forum of Mathematics, Sigma 14 (2026), e41.
These declarations specify the original targets. Their proofs are supplied in
ComplexRealMainAssembly and ComplexMainAssembly. The real theorem is numbered
1.1; the complex extension is an unnumbered remark recorded separately.
-/
universe u
namespace SigmaNonprimarity
open ThesisCommon

/-- Theorem 1.1, Section 1: there are a compact Hausdorff L and real Banach spaces
X, X̃ with C(L) ≃ X ⊕ X̃, neither isomorphic to any real Banach lattice.
The binary product has the max norm, a standard realization of the finite sum.
All witnesses and possible lattice representatives live in the same arbitrary universe. -/
def Theorem_1_1 : Prop :=
  ∃ (L : Compactum.{u}) (X Xtilde : RealBanachSpace.{u}),
    Nonempty (C(L, ℝ) ≃L[ℝ] (X × Xtilde)) ∧
    ¬ IsomorphicToBanachLattice X ∧ ¬ IsomorphicToBanachLattice Xtilde

/-- The unnumbered C(K) consequence immediately following Theorem 1.1. -/
def CKCounterexample : Prop :=
  ∃ (L : Compactum.{u}) (X Xtilde : RealBanachSpace.{u}),
    Nonempty (C(L, ℝ) ≃L[ℝ] (X × Xtilde)) ∧
    ¬ IsomorphicToCK X ∧ ¬ IsomorphicToCK Xtilde

end SigmaNonprimarity
