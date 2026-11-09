import BanachIsometric.AlexanderWhitneyNaturality
import BanachIsometric.RawTensorTotalDegree

/-! Actual continuous maps induce signed tensor-chain maps, preserving the
literal total degree. These identities support natural acyclic-model maps. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

theorem rawBigradedTensorMap_leftBoundary (f : C(X, X')) (g : C(Y, Y')) :
    (rawBigradedTensorMap f g).comp (rawTensorLeftBoundary X Y) =
      (rawTensorLeftBoundary X' Y').comp (rawBigradedTensorMap f g) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawBigradedTensorMap f g
      (rawTensorLeftBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) =
    rawTensorLeftBoundary X' Y'
      (rawBigradedTensorMap f g (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)))
  cases p with
  | zero => simp [rawBigradedTensorMap_inclusion, rawTensorLeftBoundary_inclusion, rawTensorLeftComponent]
  | succ p =>
    rw [rawTensorLeftBoundary_tmul, rawBigradedTensorMap_inclusion, TensorProduct.map_tmul,
      rawBigradedTensorMap_inclusion, TensorProduct.map_tmul, rawTensorLeftBoundary_tmul]
    have h := LinearMap.congr_fun (rawChainMap_boundary f p) c
    change rawBoundary p (rawChainMap f (p + 1) c) = rawChainMap f p (rawBoundary p c) at h
    rw [h]

theorem rawBigradedTensorMap_rightBoundary (f : C(X, X')) (g : C(Y, Y')) :
    (rawBigradedTensorMap f g).comp (rawTensorRightBoundary X Y) =
      (rawTensorRightBoundary X' Y').comp (rawBigradedTensorMap f g) := by
  apply DirectSum.linearMap_ext
  rintro ⟨p, q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro d
  change rawBigradedTensorMap f g
      (rawTensorRightBoundary X Y (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d))) =
    rawTensorRightBoundary X' Y'
      (rawBigradedTensorMap f g (rawTensorInclusion X Y p q (c ⊗ₜ[ℚ] d)))
  cases q with
  | zero => simp [rawBigradedTensorMap_inclusion, rawTensorRightBoundary_inclusion, rawTensorRightComponent]
  | succ q =>
    rw [rawTensorRightBoundary_tmul, map_smul, rawBigradedTensorMap_inclusion, TensorProduct.map_tmul,
      rawBigradedTensorMap_inclusion, TensorProduct.map_tmul, rawTensorRightBoundary_tmul]
    have h := LinearMap.congr_fun (rawChainMap_boundary g q) d
    change rawBoundary q (rawChainMap g (q + 1) d) = rawChainMap g q (rawBoundary q d) at h
    rw [h]

theorem rawBigradedTensorMap_boundary (f : C(X, X')) (g : C(Y, Y')) :
    (rawBigradedTensorMap f g).comp (rawTensorTotalBoundary X Y) =
      (rawTensorTotalBoundary X' Y').comp (rawBigradedTensorMap f g) := by
  apply LinearMap.ext
  intro c
  have hL := LinearMap.congr_fun (rawBigradedTensorMap_leftBoundary f g) c
  have hR := LinearMap.congr_fun (rawBigradedTensorMap_rightBoundary f g) c
  simp only [LinearMap.comp_apply] at hL hR
  change rawBigradedTensorMap f g
      (rawTensorLeftBoundary X Y c + rawTensorRightBoundary X Y c) =
    rawTensorLeftBoundary X' Y' (rawBigradedTensorMap f g c) +
      rawTensorRightBoundary X' Y' (rawBigradedTensorMap f g c)
  rw [map_add, hL, hR]

theorem rawBigradedTensorMap_component (f : C(X, X')) (g : C(Y, Y')) (p q : ℕ)
    (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X' Y' p q (rawBigradedTensorMap f g c) =
      TensorProduct.map (rawChainMap f p) (rawChainMap g q) (rawTensorComponent X Y p q c) := by
  have h : (rawTensorComponent X' Y' p q).comp (rawBigradedTensorMap f g) =
      (TensorProduct.map (rawChainMap f p) (rawChainMap g q)).comp (rawTensorComponent X Y p q) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro x
    change rawTensorComponent X' Y' p q (rawBigradedTensorMap f g (rawTensorInclusion X Y r s x)) =
      TensorProduct.map (rawChainMap f p) (rawChainMap g q)
        (rawTensorComponent X Y p q (rawTensorInclusion X Y r s x))
    rw [rawBigradedTensorMap_inclusion]
    by_cases he : (r, s) = (p, q)
    · have hr := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      change r = p at hr
      change s = q at hs
      subst r
      subst s
      rw [rawTensorComponent_inclusion, rawTensorComponent_inclusion]
    · rw [rawTensorComponent_inclusion_of_ne X' Y' he,
        rawTensorComponent_inclusion_of_ne X Y he, map_zero]
  exact LinearMap.congr_fun h c

theorem rawBigradedTensorMap_mem_totalDegree (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    {c : RawBigradedTensorChains X Y} (hc : c ∈ rawTensorTotalDegree X Y n) :
    rawBigradedTensorMap f g c ∈ rawTensorTotalDegree X' Y' n := by
  intro p q hpq
  rw [rawBigradedTensorMap_component, hc p q hpq, map_zero]

def rawBigradedTensorMapHomogeneous (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    rawTensorTotalDegree X Y n →ₗ[ℚ] rawTensorTotalDegree X' Y' n :=
  LinearMap.codRestrict (rawTensorTotalDegree X' Y' n)
    ((rawBigradedTensorMap f g).comp (rawTensorTotalDegree X Y n).subtype)
    (fun c => rawBigradedTensorMap_mem_totalDegree f g n c.property)

theorem rawBigradedTensorMapHomogeneous_boundary (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) :
    (rawTensorBoundary X' Y' n).comp (rawBigradedTensorMapHomogeneous f g (n + 1)) =
      (rawBigradedTensorMapHomogeneous f g n).comp (rawTensorBoundary X Y n) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact (LinearMap.congr_fun (rawBigradedTensorMap_boundary f g) c.val).symm

end BanachIsometric.SingularAW
