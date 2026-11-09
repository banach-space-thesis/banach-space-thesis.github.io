import BanachIsometric.AlexanderWhitneyChainMap
import BanachIsometric.RawTensorTotalDegree

/-! Alexander--Whitney as an actual map of nonnegative chain families,
landing in the genuine homogeneous total-degree tensor submodules. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem rawAlexanderWhitneyHomogeneous_boundary (n : ℕ) :
    (rawTensorBoundary X Y n).comp (rawAlexanderWhitneyHomogeneous X Y (n + 1)) =
      (rawAlexanderWhitneyHomogeneous X Y n).comp (rawBoundary n) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change rawTensorTotalBoundary X Y (rawAlexanderWhitney (n + 1) c) =
    rawAlexanderWhitney n (rawBoundary n c)
  exact LinearMap.congr_fun (rawAlexanderWhitney_boundary n) c

def rawAlexanderWhitneyDiagonalHomogeneous (n : ℕ) :
    RawRationalChains X n →ₗ[ℚ] rawTensorTotalDegree X X n :=
  LinearMap.codRestrict (rawTensorTotalDegree X X n) (rawAlexanderWhitneyDiagonal n) (by
    intro c
    apply rawAlexanderWhitney_mem_totalDegree)

theorem rawAlexanderWhitneyDiagonalHomogeneous_boundary (n : ℕ) :
    (rawTensorBoundary X X n).comp (rawAlexanderWhitneyDiagonalHomogeneous (X := X) (n + 1)) =
      (rawAlexanderWhitneyDiagonalHomogeneous (X := X) n).comp (rawBoundary n) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change rawTensorTotalBoundary X X (rawAlexanderWhitneyDiagonal (n + 1) c) =
    rawAlexanderWhitneyDiagonal n (rawBoundary n c)
  exact LinearMap.congr_fun (rawAlexanderWhitneyDiagonal_boundary n) c

end BanachIsometric.SingularAW
