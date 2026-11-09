import BanachIsometric.RawTensorDeformation
import BanachIsometric.RawTensorHomotopyDegrees
import BanachIsometric.RawAcyclicFillers

/-! Actual fillings for cycles of the genuine homogeneous tensor complex on
contractible factors. The zero-degree condition is exactly the literal product
augmentation. Universal simplex-pair models require no additional hypotheses. -/

noncomputable section
namespace BanachIsometric.SingularAW
open SingularPrism
open scoped TensorProduct

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

def rawTensorHomogeneousHomotopy (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] rawTensorTotalDegree X Y (n + 1) :=
  ((rawTensorTotalHomotopy X Y).comp (rawTensorTotalDegree X Y n).subtype).codRestrict
    (rawTensorTotalDegree X Y (n + 1))
    (fun c => rawTensorTotalHomotopy_mem_totalDegree X Y n c.property)

theorem rawTensorHomogeneousHomotopy_fills [ContractibleSpace X] [ContractibleSpace Y]
    (n : ℕ) (c : rawTensorTotalDegree X Y n)
    (hc : rawTensorTotalBoundary X Y c.val = 0)
    (ha : n = 0 → rawTensorAugmentation X Y c.val = 0) :
    rawTensorTotalBoundary X Y (rawTensorHomogeneousHomotopy X Y n c).val = c.val := by
  have hp : rawTensorBothProjector X Y c.val = 0 := by
    cases n with
    | zero =>
        exact rawTensorBothProjector_eq_zero_of_zero_totalDegree_augmentation X Y c.property (ha rfl)
    | succ n => exact rawTensorBothProjector_eq_zero_of_positive_totalDegree X Y n c.property
  have h := rawTensorBoundary_totalHomotopy_of_cycle X Y hc
  rwa [hp, add_zero] at h

theorem exists_rawTensor_positive_cycle_filler [ContractibleSpace X] [ContractibleSpace Y]
    (n : ℕ) (c : rawTensorTotalDegree X Y (n + 1)) (hc : rawTensorBoundary X Y n c = 0) :
    ∃ b : rawTensorTotalDegree X Y (n + 2), rawTensorBoundary X Y (n + 1) b = c := by
  refine ⟨rawTensorHomogeneousHomotopy X Y (n + 1) c, ?_⟩
  apply Subtype.ext
  have hz := congrArg Subtype.val hc
  exact rawTensorHomogeneousHomotopy_fills X Y (n + 1) c hz (by intro hn; omega)

theorem exists_rawTensor_zero_cycle_filler [ContractibleSpace X] [ContractibleSpace Y]
    (c : rawTensorTotalDegree X Y 0) (ha : rawTensorAugmentation X Y c.val = 0) :
    ∃ b : rawTensorTotalDegree X Y 1, rawTensorBoundary X Y 0 b = c := by
  refine ⟨rawTensorHomogeneousHomotopy X Y 0 c, ?_⟩
  apply Subtype.ext
  exact rawTensorHomogeneousHomotopy_fills X Y 0 c
    (rawTensorTotalBoundary_eq_zero_of_totalDegree_zero X Y c.property) (fun _ => ha)

theorem simplex_pair_tensor_cycle_fills (p q n : ℕ)
    (c : rawTensorTotalDegree (Simplex p) (Simplex q) n)
    (hc : rawTensorTotalBoundary (Simplex p) (Simplex q) c.val = 0)
    (ha : n = 0 → rawTensorAugmentation (Simplex p) (Simplex q) c.val = 0) :
    ∃ b : rawTensorTotalDegree (Simplex p) (Simplex q) (n + 1),
      rawTensorTotalBoundary (Simplex p) (Simplex q) b.val = c.val := by
  letI := simplex_contractible p
  letI := simplex_contractible q
  exact ⟨rawTensorHomogeneousHomotopy (Simplex p) (Simplex q) n c,
    rawTensorHomogeneousHomotopy_fills (Simplex p) (Simplex q) n c hc ha⟩

end BanachIsometric.SingularAW
