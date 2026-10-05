import Sigma.ComplexMainAssembly
import Sigma.ComplexCKLattice

/-! The complex C(K) and class-primariness consequences of the fully
constructed complex decomposition. All existence and representation
inputs have been discharged. -/
noncomputable section
universe u
namespace SigmaNonprimarity
open ThesisCommon

theorem complex_ckCounterexample_completed : ComplexCKCounterexample.{u} := by
  obtain ⟨K,X,Y,e,hX,hY⟩ := complex_theorem_1_1_completed.{u}
  exact ⟨K,X,Y,e,fun h => hX (isomorphicToComplexCK_implies_lattice h),
    fun h => hY (isomorphicToComplexCK_implies_lattice h)⟩

theorem complex_latticeClass_not_primary_completed :
    ¬ IsComplexPrimaryClass
      (fun X : ComplexBanachSpace.{u} => IsomorphicToComplexBanachLattice X) := by
  obtain ⟨K,X,Y,e,hX,hY⟩ := complex_theorem_1_1_completed.{u}
  intro hprimary
  have hsplit := hprimary { Carrier := C(K,ℂ) } X Y
    (complex_ck_isomorphicToBanachLattice K) e
  exact hsplit.elim hX hY

theorem complex_ckClass_not_primary_completed :
    ¬ IsComplexPrimaryClass
      (fun X : ComplexBanachSpace.{u} => IsomorphicToComplexCK X) := by
  obtain ⟨K,X,Y,e,hX,hY⟩ := complex_ckCounterexample_completed.{u}
  intro hprimary
  have hsplit := hprimary { Carrier := C(K,ℂ) } X Y
    ⟨K,⟨ContinuousLinearEquiv.refl ℂ C(K,ℂ)⟩⟩ e
  exact hsplit.elim hX hY

end SigmaNonprimarity
