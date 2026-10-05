import JLMS.Definitions
import Mathlib.Data.Matrix.Basis
import Mathlib.Topology.Instances.Matrix

/-!
# Section 9: automatic continuity passes to finite matrix algebras

Diagonal corners are algebra homomorphisms. Each off-diagonal corner factors
as a diagonal corner multiplied by a fixed matrix unit. The finite sum of
corner maps recovers the homomorphism, exactly as in the paper. The topology
is the finite product topology, so this applies to all equivalent matrix norms.
-/

noncomputable section
namespace JLMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {B : Type*} [NormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixDiagonalCorner (i : n) : B →ₙₐ[𝕜] Matrix n n B where
  toFun b := Matrix.single i i b
  map_zero' := by
    classical
    ext r s
    simp [Matrix.single]
  map_add' b c := Matrix.single_add i i b c
  map_smul' c b := (Matrix.smul_single c i i b).symm
  map_mul' b c := by
    classical
    exact (Matrix.single_mul_single_same (c := b) i i i c).symm

theorem continuous_matrix_hom_of_corners
    (hB : ∀ f : B →ₙₐ[𝕜] A, Continuous f)
    (θ : Matrix n n B →ₙₐ[𝕜] A) : Continuous θ := by
  let ψ (i : n) := θ.comp (matrixDiagonalCorner (𝕜 := 𝕜) (B := B) i)
  have hψ (i : n) : Continuous (ψ i) := hB _
  have hcorner (i j : n) : Continuous (fun b : B => θ (Matrix.single i j b)) := by
    have heq (b : B) : θ (Matrix.single i j b) = ψ i b * θ (Matrix.single i j 1) := by
      change θ (Matrix.single i j b) = θ (Matrix.single i i b) * θ (Matrix.single i j 1)
      rw [← map_mul, Matrix.single_mul_single_same, mul_one]
    convert (hψ i).mul (continuous_const (y := θ (Matrix.single i j 1))) using 1
    funext b
    exact heq b
  have hsum : Continuous (fun M : Matrix n n B => ∑ i, ∑ j, θ (Matrix.single i j (M i j))) := by
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro j hj
    exact (hcorner i j).comp (continuous_apply_apply i j)
  convert hsum using 1
  funext M
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]

end JLMS
