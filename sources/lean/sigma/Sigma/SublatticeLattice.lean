import Sigma.ModulusEmbedding
import ThesisCommon.Analysis.CKLattice
import Mathlib.Order.Sublattice

noncomputable section
universe u
namespace SigmaNonprimarity
open ThesisCommon
open scoped BoundedContinuousFunction

theorem lattice_of_sublattice (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : IsomorphicToSublatticeEllInfinity E) : IsomorphicToBanachLattice E := by
  obtain ⟨S, hclosed, hlat, ⟨T⟩⟩ := h
  letI : NormedAddCommGroup S := inferInstance
  letI : NormedSpace ℝ S := inferInstance
  let L : Sublattice (ℕ →ᵇ ℝ) :=
    { carrier := S
      supClosed' := fun _ hf _ hg => (hlat _ hf _ hg).1
      infClosed' := fun _ hf _ hg => (hlat _ hf _ hg).2 }
  letI : Lattice S := L.instLatticeCoe
  letI : IsOrderedAddMonoid S :=
    { add_le_add_left := by
        intro a b h c
        change c.val + a.val ≤ c.val + b.val
        exact add_le_add_left (show a.val ≤ b.val from h) c.val }
  letI : IsOrderedModule ℝ S :=
    { smul_le_smul_of_nonneg_left := fun r hr a b h =>
        show r • a.val ≤ r • b.val from smul_le_smul_of_nonneg_left h hr
      smul_le_smul_of_nonneg_right := fun a ha r s hrs =>
        show r • a.val ≤ s • a.val from smul_le_smul_of_nonneg_right hrs ha }
  letI : HasSolidNorm S := ⟨fun a b h =>
    show ‖a.val‖ ≤ ‖b.val‖ from norm_le_norm_of_abs_le_abs h⟩
  letI : CompleteSpace S := hclosed.completeSpace_coe
  letI : NormedAddCommGroup (ULift.{u} S) := inferInstance
  letI : NormedSpace ℝ (ULift.{u} S) := inferInstance
  letI : IsOrderedAddMonoid (ULift.{u} S) :=
    { add_le_add_left := by
        intro a b h c
        change c.down + a.down ≤ c.down + b.down
        exact add_le_add_left (show a.down ≤ b.down from h) c.down }
  letI : IsOrderedModule ℝ (ULift.{u} S) :=
    { smul_le_smul_of_nonneg_left := fun r hr a b h =>
        show r • a.down ≤ r • b.down from smul_le_smul_of_nonneg_left h hr
      smul_le_smul_of_nonneg_right := fun a ha r s hrs =>
        show r • a.down ≤ s • a.down from smul_le_smul_of_nonneg_right hrs ha }
  letI : HasSolidNorm (ULift.{u} S) := ⟨fun a b h =>
    show ‖a.down‖ ≤ ‖b.down‖ from norm_le_norm_of_abs_le_abs h⟩
  refine ⟨{ Carrier := ULift.{u} S
            lattice := inferInstance
            orderedAdd := inferInstance
            orderedModule := inferInstance
            solidNorm := inferInstance }, ?_⟩
  exact ⟨T.trans ((LinearIsometryEquiv.ulift (R := ℝ) (E := S)).symm.toContinuousLinearEquiv)⟩

theorem lattice_of_not_desiredProperty (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (h : ¬ DesiredProperty E) :
    IsomorphicToBanachLattice E :=
  lattice_of_sublattice E (sublattice_of_not_desiredProperty E h)

end SigmaNonprimarity
