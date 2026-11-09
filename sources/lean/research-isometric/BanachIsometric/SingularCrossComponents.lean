import BanachIsometric.SingularKunnethPairing
import BanachIsometric.SingularHomologyCrossproduct

/-! The Künneth components of a pure crossproduct recover its tensor
in the stated bidegree and vanish in all other bidegrees. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

open SingularAW
open scoped TensorProduct

variable (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawKunnethHomologyComponent_cross {n p q : ℕ} (h : p + q = n)
    (a : RawHomology X p) (b : RawHomology Y q) :
    rawKunnethHomologyComponent X Y h (rawHomologyCross X Y h a b) = a ⊗ₜ[ℚ] b := by
  change rawHomologyTensorComponent X Y h
    (rawSingularKunnethEquiv X Y n (rawHomologyCross X Y h a b)) = _
  rw [rawHomologyCross_compare, rawHomologyTensorComponent_inclusion]

theorem rawKunnethHomologyComponent_cross_of_ne {n p q r s : ℕ}
    (h : p + q = n) (h' : r + s = n) (hne : (r, s) ≠ (p, q))
    (a : RawHomology X r) (b : RawHomology Y s) :
    rawKunnethHomologyComponent X Y h (rawHomologyCross X Y h' a b) = 0 := by
  change rawHomologyTensorComponent X Y h
    (rawSingularKunnethEquiv X Y n (rawHomologyCross X Y h' a b)) = 0
  rw [rawHomologyCross_compare, rawHomologyTensorComponent_inclusion_of_ne X Y h h' hne]

end BanachIsometric.SingularEZ
