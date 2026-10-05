import ThesisCommon.Analysis.SigmaComplexClassPrimariness

/-! The unnumbered complex extension in the final paragraph of the paper's
introduction. Complex lattice representatives are arbitrary intrinsic
complexifications of real Banach lattices, with their lattice modulus norm. -/
universe u
namespace SigmaNonprimarity
open ThesisCommon

def ComplexTheorem_1_1 : Prop :=
  ∃ (L : Compactum.{u}) (X Xtilde : ComplexBanachSpace.{u}),
    Nonempty (C(L, ℂ) ≃L[ℂ] (X × Xtilde)) ∧
    ¬ IsomorphicToComplexBanachLattice X ∧ ¬ IsomorphicToComplexBanachLattice Xtilde

def ComplexCKCounterexample : Prop :=
  ∃ (L : Compactum.{u}) (X Xtilde : ComplexBanachSpace.{u}),
    Nonempty (C(L, ℂ) ≃L[ℂ] (X × Xtilde)) ∧
    ¬ IsomorphicToComplexCK X ∧ ¬ IsomorphicToComplexCK Xtilde

end SigmaNonprimarity
