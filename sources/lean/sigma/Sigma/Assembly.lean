import Sigma.MainStatements
import ThesisCommon.Analysis.CKLattice
import ThesisCommon.Analysis.FiniteSums
import ThesisCommon.Analysis.ClassPrimariness

noncomputable section
universe u
namespace SigmaNonprimarity
open ThesisCommon

/-- The unnumbered C(K) consequence. CONDITIONAL: Theorem 1.1 remains an input. -/
theorem ckCounterexample_of_theorem_1_1 (h : Theorem_1_1.{u}) : CKCounterexample.{u} := by
  rcases h with ⟨L, X, Xt, e, hx, hxt⟩
  exact ⟨L, X, Xt, e, fun h => hx (isomorphicToCK_implies_lattice h),
    fun h => hxt (isomorphicToCK_implies_lattice h)⟩

/-- The title's conclusion, conditional on the still-open existence theorem. -/
theorem latticeClass_not_primary_of_theorem_1_1 (h : Theorem_1_1.{u}) :
    ¬ IsPrimaryClass (fun X : RealBanachSpace.{u} => IsomorphicToBanachLattice X) := by
  rcases h with ⟨L, X, Xt, e, hx, hxt⟩
  intro hprimary
  have hsplit := hprimary { Carrier := C(L, ℝ) } X Xt (ck_isomorphicToBanachLattice L) e
  exact hsplit.elim hx hxt

/-- The C(K)-class consequence, conditional on the still-open existence theorem. -/
theorem ckClass_not_primary_of_theorem_1_1 (h : Theorem_1_1.{u}) :
    ¬ IsPrimaryClass (fun X : RealBanachSpace.{u} => IsomorphicToCK X) := by
  rcases ckCounterexample_of_theorem_1_1 h with ⟨L, X, Xt, e, hx, hxt⟩
  intro hprimary
  have hsplit := hprimary { Carrier := C(L, ℝ) } X Xt
    ⟨L, ⟨ContinuousLinearEquiv.refl ℝ C(L, ℝ)⟩⟩ e
  exact hsplit.elim hx hxt

/-- Section 2's assembly from two decompositions and the crossed obstructions.
CONDITIONAL: no claim that the required two decompositions/obstructions exist. -/
theorem theorem_1_1_of_crossed_decompositions
    (K L : Compactum.{u}) (A B C D : RealBanachSpace.{u})
    (e : C(K, ℝ) ≃L[ℝ] (A × B)) (f : C(L, ℝ) ≃L[ℝ] (C × D))
    (hCB : ¬ IsomorphicToBanachLattice (C × B))
    (hAD : ¬ IsomorphicToBanachLattice (A × D)) : Theorem_1_1.{u} := by
  refine ⟨{ Carrier := K ⊕ L }, { Carrier := C × B }, { Carrier := A × D }, ?_, hCB, hAD⟩
  exact ⟨((continuousSumEquiv K L).trans (e.prodCongr f)).trans (crossRegroup A B C D)⟩

end SigmaNonprimarity
