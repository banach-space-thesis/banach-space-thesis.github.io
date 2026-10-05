import ThesisCommon.Analysis.ALRenormPartition
import ThesisCommon.Analysis.BanachLattice
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! The positive-partition norm as an actual equivalent Banach lattice norm.
The uniform positive-decomposition estimate is an explicit input here. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
variable (C : ℝ) (hC : 0 ≤ C)
variable (hbound : ∀ (n : ℕ) (v : Fin n → E), (∀ i, 0 ≤ v i) →
  (∑ i, ‖v i‖) ≤ C * ‖∑ i, v i‖)

/-- A type copy carrying the proved positive-partition norm. -/
def SigmaComplexPositivePartitionSpace (C : ℝ) (_hC : 0 ≤ C)
    (_hbound : ∀ (n : ℕ) (v : Fin n → E), (∀ i, 0 ≤ v i) →
      (∑ i, ‖v i‖) ≤ C * ‖∑ i, v i‖) := E

instance sigmaComplexPositivePartitionSpaceAddGroup : AddCommGroup (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  inferInstanceAs (AddCommGroup E)

instance sigmaComplexPositivePartitionSpaceModule : Module ℝ (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  inferInstanceAs (Module ℝ E)

instance sigmaComplexPositivePartitionSpaceNormedGroup :
    NormedAddCommGroup (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  AddGroupNorm.toNormedAddCommGroup
    { (positivePartitionNorm C hC hbound).toAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun x hx => by
        have hn : ‖(show E from x)‖ = 0 :=
          le_antisymm ((positivePartitionNorm_bounds C hC hbound x).1.trans_eq hx)
            (norm_nonneg (show E from x))
        exact norm_eq_zero.mp hn }

theorem sigmaComplexPositivePartitionSpace_norm (x : SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :
    ‖x‖ = positivePartitionNorm C hC hbound (show E from x) := rfl

instance sigmaComplexPositivePartitionSpaceNormedModule :
    NormedSpace ℝ (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) where
  norm_smul_le r x := (map_smul_eq_mul (positivePartitionNorm C hC hbound) r (show E from x)).le

instance sigmaComplexPositivePartitionSpaceLattice : Lattice (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  inferInstanceAs (Lattice E)

instance sigmaComplexPositivePartitionSpaceOrderedAdd :
    IsOrderedAddMonoid (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  inferInstanceAs (IsOrderedAddMonoid E)

instance sigmaComplexPositivePartitionSpaceOrderedModule :
    IsOrderedModule ℝ (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  inferInstanceAs (IsOrderedModule ℝ E)

instance sigmaComplexPositivePartitionSpaceSolid : HasSolidNorm (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) where
  solid x y h := positivePartitionFunctional_mono C hC hbound h

def sigmaComplexPositivePartitionSpaceEquiv : E ≃L[ℝ] SigmaComplexPositivePartitionSpace (E := E) C hC hbound :=
  LinearEquiv.toContinuousLinearEquivOfBounds (LinearEquiv.refl ℝ E) C 1
    (fun x => (positivePartitionNorm_bounds C hC hbound x).2)
    (fun x => by simpa only [one_mul] using (positivePartitionNorm_bounds C hC hbound x).1)

@[simp] theorem sigmaComplexPositivePartitionSpaceEquiv_apply (x : E) :
    sigmaComplexPositivePartitionSpaceEquiv C hC hbound x = x := rfl

theorem sigmaComplexPositivePartitionSpaceEquiv_nonneg (x : E) :
    0 ≤ sigmaComplexPositivePartitionSpaceEquiv C hC hbound x ↔ 0 ≤ x := Iff.rfl

instance sigmaComplexPositivePartitionSpaceComplete [CompleteSpace E] :
    CompleteSpace (SigmaComplexPositivePartitionSpace (E := E) C hC hbound) :=
  (sigmaComplexPositivePartitionSpaceEquiv C hC hbound).symm.isUniformEmbedding.isUniformInducing.completeSpace
    (by rw [(sigmaComplexPositivePartitionSpaceEquiv C hC hbound).symm.surjective.range_eq]; exact complete_univ)

theorem sigmaComplexPositivePartitionSpace_AL (x y : SigmaComplexPositivePartitionSpace (E := E) C hC hbound)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : ‖x+y‖ = ‖x‖ + ‖y‖ :=
  positivePartitionNorm_add_of_nonneg C hC hbound x y hx hy

def sigmaComplexPositivePartitionBanachLattice [CompleteSpace E] : RealBanachLattice.{u} where
  Carrier := SigmaComplexPositivePartitionSpace (E := E) C hC hbound

end ThesisCommon


