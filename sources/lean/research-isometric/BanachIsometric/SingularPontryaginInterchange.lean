import BanachIsometric.SingularPontryaginDiagonal
import BanachIsometric.SingularCrossInterchange
import Mathlib.Algebra.Algebra.Bilinear

/-! Continuous multiplication after the four-factor interchange induces
the actual Koszul multiplication after Künneth. The proof is tested on
literal homogeneous tensor generators and extends by bilinearity. -/

noncomputable section
universe u
namespace BanachIsometric.SingularEZ

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 3000

open SingularAW
open scoped DirectSum TensorProduct

variable (G : Type u) [TopologicalSpace G] [Monoid G] [ContinuousMul G]

def awMultiplicationInterchange : C((G × G) × (G × G), G × G) :=
  (awProductMap (awTopologicalMul G) (awTopologicalMul G)).comp (awProductInterchange G G G G)

theorem rawPontryaginInterchange_pure {p q i j k l : ℕ} (hp : i + j = p) (hq : k + l = q)
    (a : RawHomology G i) (b : RawHomology G j) (c : RawHomology G k) (d : RawHomology G l) :
    rawPontryaginTensorInclusion G (p + q) (rawSingularKunnethEquiv G G (p + q)
      (rawFullHomologyMap (awMultiplicationInterchange G) (p + q)
        (rawHomologyCross (G × G) (G × G) rfl (rawHomologyCross G G hp a b) (rawHomologyCross G G hq c d)))) =
      rawPontryaginTensorInclusion G p (rawHomologyTensorInclusion G G hp (a ⊗ₜ[ℚ] b)) *
        rawPontryaginTensorInclusion G q (rawHomologyTensorInclusion G G hq (c ⊗ₜ[ℚ] d)) := by
  subst p
  subst q
  rw [awMultiplicationInterchange, rawFullHomologyMap_apply_comp, rawHomologyCross_interchange, map_smul,
    rawHomologyCross_naturality, map_smul, map_smul, rawHomologyCross_compare,
    rawPontryaginTensorInclusion_tmul, rawPontryaginTensorInclusion_tmul, rawPontryaginTensorInclusion_tmul]
  rw [KoszulTensor.tmul_mul_of_mem _ _ _
      (rawPontryaginInclusion_mem_degree G j b) (rawPontryaginInclusion_mem_degree G k c),
    rawPontryaginInclusion_mul, rawPontryaginInclusion_mul]
  rfl

theorem rawPontryaginInterchange (p q : ℕ) (u : RawHomologyTensorDegree G G p)
    (v : RawHomologyTensorDegree G G q) :
    rawPontryaginTensorInclusion G (p + q) (rawSingularKunnethEquiv G G (p + q)
      (rawFullHomologyMap (awMultiplicationInterchange G) (p + q)
        (rawHomologyCross (G × G) (G × G) rfl
          ((rawSingularKunnethEquiv G G p).symm u) ((rawSingularKunnethEquiv G G q).symm v)))) =
      rawPontryaginTensorInclusion G p u * rawPontryaginTensorInclusion G q v := by
  let B := KoszulTensor (rawPontryaginDegree G)
  let f : RawHomologyTensorDegree G G p →ₗ[ℚ] RawHomologyTensorDegree G G q →ₗ[ℚ] B :=
    (((rawHomologyCross (G × G) (G × G) (rfl : p + q = p + q)).comp
      (rawSingularKunnethEquiv G G p).symm.toLinearMap).compl₂
        (rawSingularKunnethEquiv G G q).symm.toLinearMap).compr₂
          ((rawPontryaginTensorInclusion G (p + q)).comp
            ((rawSingularKunnethEquiv G G (p + q)).toLinearMap.comp
              (rawFullHomologyMap (awMultiplicationInterchange G) (p + q))))
  let g : RawHomologyTensorDegree G G p →ₗ[ℚ] RawHomologyTensorDegree G G q →ₗ[ℚ] B :=
    ((LinearMap.mul ℚ B).comp (rawPontryaginTensorInclusion G p)).compl₂ (rawPontryaginTensorInclusion G q)
  have h : f = g := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨i, j⟩, hp⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply DirectSum.linearMap_ext
    rintro ⟨⟨k, l⟩, hq⟩
    apply TensorProduct.ext
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro d
    change f (rawHomologyTensorInclusion G G hp (a ⊗ₜ[ℚ] b))
        (rawHomologyTensorInclusion G G hq (c ⊗ₜ[ℚ] d)) =
      g (rawHomologyTensorInclusion G G hp (a ⊗ₜ[ℚ] b))
        (rawHomologyTensorInclusion G G hq (c ⊗ₜ[ℚ] d))
    simpa only [f, g, LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.mul_apply_apply, rawHomologyCross_apply G G hp a b,
      rawHomologyCross_apply G G hq c d] using rawPontryaginInterchange_pure G hp hq a b c d
  simpa only [f, g, LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.mul_apply_apply] using LinearMap.congr_fun (LinearMap.congr_fun h u) v

end BanachIsometric.SingularEZ
