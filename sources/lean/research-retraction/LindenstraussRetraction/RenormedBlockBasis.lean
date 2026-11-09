import LindenstraussRetraction.BlockDecomposition
import LindenstraussRetraction.BlockBasis
import LindenstraussRetraction.ConcreteConstruction

/-! Explicit block coordinates and Schauder bases for the spaces `Y_ε`. -/

noncomputable section

namespace LindenstraussRetraction

universe v
variable (𝕜 : Type v) [RCLike 𝕜]

set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 512

local instance blockBasisAnisotropicNormedGroup (ε : ℝ) : NormedAddCommGroup (AnisotropicSpace (summationOperator 𝕜) ε) :=
  inferInstance
local instance blockBasisAnisotropicNormedSpace (ε : ℝ) : NormedSpace 𝕜 (AnisotropicSpace (summationOperator 𝕜) ε) :=
  inferInstance

def anisotropicSummationBlockBasisData {ε : ℝ} (hε : 0 < ε) :
    BlockBasisData 𝕜 (AnisotropicSpace (summationOperator 𝕜) ε) where
  size m := m+1
  size_pos m := Nat.zero_lt_succ m
  vector := anisotropicSummationScalarVector 𝕜 ε
  coord := anisotropicSummationScalarCoordinate 𝕜 ε
  biorthogonal p q := anisotropicSummationScalar_biorthogonal 𝕜 hε p.1 q.1 p.2 q.2
  projection := anisotropicSummationScalarProjection 𝕜 ε
  projection_zero := anisotropicSummationScalarProjection_zero 𝕜 ε
  projection_boundary := anisotropicSummationScalarProjection_boundary 𝕜 ε
  projection_step := anisotropicSummationScalarProjection_step 𝕜 ε
  projection_bound m r _ := norm_anisotropicSummationScalarProjection_le 𝕜 hε m r
  full_tendsto := anisotropicSummationScalarProjection_full_tendsto 𝕜 hε

def anisotropicSummationSchauderBasis {ε : ℝ} (hε : 0 < ε) :
    SchauderBasis 𝕜 (AnisotropicSpace (summationOperator 𝕜) ε) :=
  (anisotropicSummationBlockBasisData 𝕜 hε).schauderBasis

theorem norm_anisotropicSummationSchauderBasis_partialSum_le {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ‖(anisotropicSummationSchauderBasis 𝕜 hε).partialSum N‖ ≤ 3 :=
  (anisotropicSummationBlockBasisData 𝕜 hε).norm_schauderBasis_partialSum_le N

/-- The concrete packets for `Y_(n+1)` used in the auxiliary c₀ sum. -/
def renormedSummationBlockBasisData (n : ℕ) :
    BlockBasisData 𝕜 (RenormedSummationSpace 𝕜 n) :=
  anisotropicSummationBlockBasisData 𝕜 (coordinateScale_pos n)

end LindenstraussRetraction
