import BanachIsometric.SingularPontryaginGrading

/-! The actual topological diagonal on singular homology, followed by
Künneth and insertion into the separately tagged Koszul tensor algebra. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open SingularAW
open scoped DirectSum TensorProduct

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

def awTopologicalDiagonal : C(G, G × G) := ⟨fun g => (g, g), continuous_id.prodMk continuous_id⟩

def rawPontryaginTensorInclusion (n : ℕ) :
    RawHomologyTensorDegree G G n →ₗ[ℚ] KoszulTensor (rawPontryaginDegree G) :=
  (KoszulTensor.tensorLinearEquiv (rawPontryaginDegree G)).symm.toLinearMap.comp
    (DirectSum.toModule ℚ (HomologyBidegrees n) (RawPontryaginAlgebra G ⊗[ℚ] RawPontryaginAlgebra G)
      (fun ij => TensorProduct.map (rawPontryaginInclusion G ij.val.1) (rawPontryaginInclusion G ij.val.2)))

theorem rawPontryaginTensorInclusion_tmul {n p q : ℕ} (h : p + q = n)
    (a : RawHomology G p) (b : RawHomology G q) :
    rawPontryaginTensorInclusion G n (rawHomologyTensorInclusion G G h (a ⊗ₜ[ℚ] b)) =
      KoszulTensor.tmul (rawPontryaginDegree G) (rawPontryaginInclusion G p a) (rawPontryaginInclusion G q b) := by
  simp only [rawPontryaginTensorInclusion, LinearMap.comp_apply, rawHomologyTensorInclusion,
    DirectSum.toModule_lof, TensorProduct.map_tmul]
  rfl

def rawPontryaginDiagonal (n : ℕ) : RawHomology G n →ₗ[ℚ] KoszulTensor (rawPontryaginDegree G) :=
  (rawPontryaginTensorInclusion G n).comp
    ((rawSingularKunnethEquiv G G n).toLinearMap.comp (rawFullHomologyMap (awTopologicalDiagonal G) n))

theorem rawPontryaginDiagonal_one : rawPontryaginDiagonal G 0 (rawPontryaginUnit G) = 1 := by
  have hpoint : rawHomologyCross G G (rfl : 0 + 0 = 0) (rawPontryaginUnit G) (rawPontryaginUnit G) =
      rawHomologyPoint (G × G) (1, 1) := by
    rw [rawPontryaginUnit, rawHomologyCross_point_right, rawFullHomologyMap_point]
    rfl
  change rawPontryaginTensorInclusion G 0
    (rawSingularKunnethEquiv G G 0
      (rawFullHomologyMap (awTopologicalDiagonal G) 0 (rawHomologyPoint G 1))) = 1
  rw [rawFullHomologyMap_point]
  change rawPontryaginTensorInclusion G 0
    (rawSingularKunnethEquiv G G 0 (rawHomologyPoint (G × G) (1, 1))) = 1
  rw [← hpoint, rawHomologyCross_compare, rawPontryaginTensorInclusion_tmul,
    rawPontryaginInclusion_one G]
  rfl

end BanachIsometric.SingularEZ
