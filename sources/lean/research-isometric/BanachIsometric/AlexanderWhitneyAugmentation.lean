import BanachIsometric.RawTensorComponents
import BanachIsometric.RawTensorAugmentation

/-! Alexander--Whitney preserves the literal product augmentation in degree
zero. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem rawAlexanderWhitney_augmentation :
    (rawTensorAugmentation X Y).comp (rawAlexanderWhitney (X := X) (Y := Y) 0) =
      rawAugmentation (X × Y) := by
  apply Finsupp.lhom_ext
  intro σ a
  change rawTensorZeroAugmentation X Y
    (rawTensorComponent X Y 0 0 (rawAlexanderWhitney 0 (Finsupp.single σ a))) =
    rawAugmentation (X × Y) (Finsupp.single σ a)
  rw [rawAlexanderWhitney_component_single X Y rfl, map_smul, awPureTerm,
    rawTensorZeroAugmentation_tmul, rawAugmentation_single, rawAugmentation_single,
    rawAugmentation_single]
  simp [smul_eq_mul]

end BanachIsometric.SingularAW
