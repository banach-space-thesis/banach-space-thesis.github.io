import BanachIsometric.RawSingularHomology
import BanachIsometric.RawZeroSingularHomology

/-! Homeomorphisms induce actual linear equivalences on the concrete singular
homology quotients, including degree zero. Both inverse identities follow
from the actual chain-functor composition and identity formulas. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def homeomorphContinuousMap (e : X ≃ₜ Y) : C(X, Y) := ⟨e, e.continuous⟩

@[simp] theorem homeomorphContinuousMap_symm_comp (e : X ≃ₜ Y) :
    (homeomorphContinuousMap e.symm).comp (homeomorphContinuousMap e) =
      ContinuousMap.id X := by
  ext x
  exact e.symm_apply_apply x

@[simp] theorem homeomorphContinuousMap_comp_symm (e : X ≃ₜ Y) :
    (homeomorphContinuousMap e).comp (homeomorphContinuousMap e.symm) =
      ContinuousMap.id Y := by
  ext y
  exact e.apply_symm_apply y

def rawPositiveHomologyHomeomorph (e : X ≃ₜ Y) (n : ℕ) :
    RawPositiveHomology X n ≃ₗ[ℚ] RawPositiveHomology Y n where
  toLinearMap := rawHomologyMap (homeomorphContinuousMap e) n
  invFun := rawHomologyMap (homeomorphContinuousMap e.symm) n
  left_inv x := by
    have h := LinearMap.congr_fun
      (rawHomologyMap_comp (homeomorphContinuousMap e) (homeomorphContinuousMap e.symm) n) x
    simpa only [homeomorphContinuousMap_symm_comp, rawHomologyMap_id,
      LinearMap.id_apply, LinearMap.comp_apply] using h.symm
  right_inv y := by
    have h := LinearMap.congr_fun
      (rawHomologyMap_comp (homeomorphContinuousMap e.symm) (homeomorphContinuousMap e) n) y
    simpa only [homeomorphContinuousMap_comp_symm, rawHomologyMap_id,
      LinearMap.id_apply, LinearMap.comp_apply] using h.symm

def rawZeroHomologyHomeomorph (e : X ≃ₜ Y) : RawZeroHomology X ≃ₗ[ℚ] RawZeroHomology Y where
  toLinearMap := rawZeroHomologyMap (homeomorphContinuousMap e)
  invFun := rawZeroHomologyMap (homeomorphContinuousMap e.symm)
  left_inv x := by
    have h := LinearMap.congr_fun
      (rawZeroHomologyMap_comp (homeomorphContinuousMap e) (homeomorphContinuousMap e.symm)) x
    simpa only [homeomorphContinuousMap_symm_comp, rawZeroHomologyMap_id,
      LinearMap.id_apply, LinearMap.comp_apply] using h.symm
  right_inv y := by
    have h := LinearMap.congr_fun
      (rawZeroHomologyMap_comp (homeomorphContinuousMap e.symm) (homeomorphContinuousMap e)) y
    simpa only [homeomorphContinuousMap_comp_symm, rawZeroHomologyMap_id,
      LinearMap.id_apply, LinearMap.comp_apply] using h.symm

end BanachIsometric.SingularPrism
