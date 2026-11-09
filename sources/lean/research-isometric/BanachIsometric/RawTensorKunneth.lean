import BanachIsometric.RawTensorHomologyIdentities
import BanachIsometric.RawTensorAcyclicFillers
import BanachIsometric.RawTensorAddCommGroup

/-! Actual rational Künneth comparison for the signed total tensor complex.
Both sides are constructed from genuine cycles modulo boundaries. The
inverse sends a tensor of classes to the class of a tensor of cycles. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

abbrev rawTensorFactorObjects (n : ℕ) := ModuleCat.of ℚ (rawTensorTotalDegree X Y n)

abbrev RawTensorHomology (n : ℕ) :=
  VectorChainSplitting.Homology (rawTensorFactorObjects X Y) (rawTensorBoundary X Y)
    (rawTensorBoundary_squared X Y) n

abbrev rawTensorCycles (n : ℕ) :=
  VectorChainSplitting.cycles (rawTensorFactorObjects X Y) (rawTensorBoundary X Y) n

abbrev rawTensorBoundaries (n : ℕ) :=
  VectorChainSplitting.boundaries (rawTensorFactorObjects X Y) (rawTensorBoundary X Y)
    (rawTensorBoundary_squared X Y) n

abbrev rawTensorCycleBoundary (n : ℕ) :=
  VectorChainSplitting.boundaryMap (rawTensorFactorObjects X Y) (rawTensorBoundary X Y)
    (rawTensorBoundary_squared X Y) n

theorem rawTensorCycles_totalBoundary_zero (n : ℕ) (c : rawTensorCycles X Y n) :
    rawTensorTotalBoundary X Y c.val.val = 0 := by
  cases n with
  | zero => exact rawTensorTotalBoundary_eq_zero_of_totalDegree_zero X Y c.val.property
  | succ n =>
    have h : rawTensorBoundary X Y n c.val = 0 := c.property
    exact congrArg Subtype.val h

def rawTensorCyclesOfTotalBoundaryZero (n : ℕ) (c : rawTensorTotalDegree X Y n)
    (h : rawTensorTotalBoundary X Y c.val = 0) : rawTensorCycles X Y n :=
  ⟨c, by
    cases n with
    | zero => trivial
    | succ n =>
      change rawTensorBoundary X Y n c = 0
      exact Subtype.ext h⟩

def rawTensorHomologyInclusionCycles (n : ℕ) :
    RawHomologyTensorDegree X Y n →ₗ[ℚ] rawTensorCycles X Y n :=
  (rawTensorHomologyInclusion X Y n).codRestrict (rawTensorCycles X Y n)
    (fun c => (rawTensorCyclesOfTotalBoundaryZero X Y n _ (rawTensorHomologyInclusion_cycle X Y n c)).property)

def rawTensorKunnethComparison (n : ℕ) : RawTensorHomology X Y n →ₗ[ℚ] RawHomologyTensorDegree X Y n :=
  (rawTensorBoundaries X Y n).liftQ
    ((rawTensorHomologyProjection X Y n).comp (rawTensorCycles X Y n).subtype)
    (by
      rintro _ ⟨b, rfl⟩
      change rawTensorHomologyProjectionTotal X Y n (rawTensorTotalBoundary X Y b.val) = 0
      exact rawTensorHomologyProjectionTotal_boundary X Y n b.val)

def rawTensorKunnethInverse (n : ℕ) : RawHomologyTensorDegree X Y n →ₗ[ℚ] RawTensorHomology X Y n :=
  (rawTensorBoundaries X Y n).mkQ.comp (rawTensorHomologyInclusionCycles X Y n)

theorem rawTensorKunnethComparison_inverse (n : ℕ) (a : RawHomologyTensorDegree X Y n) :
    rawTensorKunnethComparison X Y n (rawTensorKunnethInverse X Y n a) = a :=
  rawTensorHomologyProjection_inclusion X Y n a

theorem rawTensorKunnethInverse_comparison (n : ℕ) (a : RawTensorHomology X Y n) :
    rawTensorKunnethInverse X Y n (rawTensorKunnethComparison X Y n a) = a := by
  induction a using Submodule.Quotient.induction_on with
  | H c =>
    let b := rawTensorHomogeneousHomotopy X Y n c.val
    let u := rawTensorHomologyInclusionCycles X Y n (rawTensorHomologyProjection X Y n c.val)
    have h : rawTensorCycleBoundary X Y n b + u = c := by
      apply Subtype.ext
      apply Subtype.ext
      change rawTensorTotalBoundary X Y (rawTensorTotalHomotopy X Y c.val.val) +
        (rawTensorHomologyInclusion X Y n (rawTensorHomologyProjection X Y n c.val)).val = c.val.val
      rw [rawTensorHomologyInclusion_projection]
      exact rawTensorBoundary_totalHomotopy_of_cycle X Y (rawTensorCycles_totalBoundary_zero X Y n c)
    have hb : (rawTensorBoundaries X Y n).mkQ (rawTensorCycleBoundary X Y n b) = 0 :=
      (Submodule.Quotient.mk_eq_zero (rawTensorBoundaries X Y n)).mpr ⟨b, rfl⟩
    change (rawTensorBoundaries X Y n).mkQ u = (rawTensorBoundaries X Y n).mkQ c
    rw [← h, map_add, hb, zero_add]

def rawTensorKunnethEquiv (n : ℕ) : RawTensorHomology X Y n ≃ₗ[ℚ] RawHomologyTensorDegree X Y n :=
  { rawTensorKunnethComparison X Y n with
    invFun := rawTensorKunnethInverse X Y n
    left_inv := rawTensorKunnethInverse_comparison X Y n
    right_inv := rawTensorKunnethComparison_inverse X Y n }

end BanachIsometric.SingularAW
