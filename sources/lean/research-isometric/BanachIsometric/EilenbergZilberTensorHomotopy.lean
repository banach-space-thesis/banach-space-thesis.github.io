import BanachIsometric.EilenbergZilberTensorModelIdentity
import BanachIsometric.RawTensorAcyclicFillers

/-! The actual contraction of the simplex-pair tensor models supplies
a chain homotopy from Alexander--Whitney after crossproduct to the identity
on the literal homogeneous tensor complex. -/

noncomputable section
namespace BanachIsometric.SingularEZ

open SingularPrism SingularAW

def universalTensorHomotopyFamily : (n : ℕ) → UniversalTensorHomotopies n
  | 0 => fun p q h => rawTensorHomogeneousHomotopy (Simplex p) (Simplex q) 0 (tensorModelDifference h)
  | n + 1 => fun p q h => rawTensorHomogeneousHomotopy (Simplex p) (Simplex q) (n + 1)
      (tensorModelHomotopyCandidate (universalTensorHomotopyFamily n) h)

theorem universalTensorHomotopyFamily_zero (p q : ℕ) (h : p + q = 0) :
    rawTensorBoundary (Simplex p) (Simplex q) 0 (universalTensorHomotopyFamily 0 p q h) =
      tensorModelDifference h := by
  letI := simplex_contractible p
  letI := simplex_contractible q
  apply Subtype.ext
  apply rawTensorHomogeneousHomotopy_fills
  · exact rawTensorTotalBoundary_eq_zero_of_totalDegree_zero _ _ (tensorModelDifference h).property
  · intro _
    change rawTensorAugmentation (Simplex p) (Simplex q)
      ((rawTensorComposite 0 (universalTensorHomogeneousGenerator h)).val -
        (universalTensorHomogeneousGenerator h).val) = 0
    rw [map_sub, rawTensorComposite_augmentation, sub_self]

theorem universalTensorHomotopyFamily_succ (n : ℕ) (p q : ℕ) (h : p + q = n + 1) :
    rawTensorBoundary (Simplex p) (Simplex q) (n + 1) (universalTensorHomotopyFamily (n + 1) p q h) =
      tensorModelHomotopyCandidate (universalTensorHomotopyFamily n) h := by
  induction n generalizing p q with
  | zero =>
    letI := simplex_contractible p
    letI := simplex_contractible q
    apply Subtype.ext
    apply rawTensorHomogeneousHomotopy_fills
    · have hz : rawTensorBoundary (Simplex p) (Simplex q) 0
          (tensorModelHomotopyCandidate (universalTensorHomotopyFamily 0) h) = 0 := by
        simp only [tensorModelHomotopyCandidate, tensorModelDifference, map_sub,
          rawTensorComposite_boundary, tensorHomotopy_zero_of_model universalTensorHomotopyFamily_zero,
          sub_self]
      exact congrArg Subtype.val hz
    · omega
  | succ n ih =>
    letI := simplex_contractible p
    letI := simplex_contractible q
    apply Subtype.ext
    apply rawTensorHomogeneousHomotopy_fills
    · have hdd := LinearMap.congr_fun (rawTensorBoundary_squared (Simplex p) (Simplex q) n)
        (universalTensorHomogeneousGenerator h)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
      have hz : rawTensorBoundary (Simplex p) (Simplex q) (n + 1)
          (tensorModelHomotopyCandidate (universalTensorHomotopyFamily (n + 1)) h) = 0 := by
        simp only [tensorModelHomotopyCandidate, tensorModelDifference, map_sub,
          rawTensorComposite_boundary, tensorHomotopy_succ_of_model ih, hdd, map_zero, sub_zero, sub_self]
      exact congrArg Subtype.val hz
    · omega

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def rawTensorEZHomotopy (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] rawTensorTotalDegree X Y (n + 1) :=
  universalTensorHomotopyEvaluation (universalTensorHomotopyFamily n)

theorem rawTensorEZHomotopy_zero (c : rawTensorTotalDegree X Y 0) :
    rawTensorBoundary X Y 0 (rawTensorEZHomotopy 0 c) = rawTensorComposite 0 c - c :=
  tensorHomotopy_zero_of_model universalTensorHomotopyFamily_zero c

theorem rawTensorEZHomotopy_succ (n : ℕ) (c : rawTensorTotalDegree X Y (n + 1)) :
    rawTensorBoundary X Y (n + 1) (rawTensorEZHomotopy (n + 1) c) +
      rawTensorEZHomotopy n (rawTensorBoundary X Y n c) = rawTensorComposite (n + 1) c - c := by
  change rawTensorBoundary X Y (n + 1)
    (universalTensorHomotopyEvaluation (universalTensorHomotopyFamily (n + 1)) c) +
      universalTensorHomotopyEvaluation (universalTensorHomotopyFamily n) (rawTensorBoundary X Y n c) = _
  rw [tensorHomotopy_succ_of_model (universalTensorHomotopyFamily_succ n), sub_add_cancel]

end BanachIsometric.SingularEZ
