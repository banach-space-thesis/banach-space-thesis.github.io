import BanachIsometric.RawTensorComponents
import BanachIsometric.RawTensorBoundarySquared

/-! Actual homogeneous total-degree submodules of the raw tensor
bicomplex, with their genuine nonnegative chain boundary. -/

noncomputable section
namespace BanachIsometric.SingularAW

open SingularPrism
open scoped TensorProduct

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

theorem rawTensorComponent_leftBoundary (p q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y p q (rawTensorLeftBoundary X Y c) =
      TensorProduct.map (rawBoundary p) LinearMap.id (rawTensorComponent X Y (p + 1) q c) := by
  have h : (rawTensorComponent X Y p q).comp (rawTensorLeftBoundary X Y) =
      (TensorProduct.map (rawBoundary p) LinearMap.id).comp (rawTensorComponent X Y (p + 1) q) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro x
    change rawTensorComponent X Y p q (rawTensorLeftBoundary X Y (rawTensorInclusion X Y r s x)) =
      TensorProduct.map (rawBoundary p) LinearMap.id
        (rawTensorComponent X Y (p + 1) q (rawTensorInclusion X Y r s x))
    by_cases he : (r, s) = (p + 1, q)
    · have hr := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      change r = p + 1 at hr
      change s = q at hs
      subst r
      subst s
      rw [rawTensorComponent_left_inclusion, rawTensorComponent_inclusion]
    · rw [rawTensorComponent_left_inclusion_of_ne X Y he,
        rawTensorComponent_inclusion_of_ne X Y he, map_zero]
  exact LinearMap.congr_fun h c

theorem rawTensorComponent_rightBoundary (p q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y p q (rawTensorRightBoundary X Y c) =
      (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q)
        (rawTensorComponent X Y p (q + 1) c) := by
  have h : (rawTensorComponent X Y p q).comp (rawTensorRightBoundary X Y) =
      ((-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q)).comp
        (rawTensorComponent X Y p (q + 1)) := by
    apply DirectSum.linearMap_ext
    rintro ⟨r, s⟩
    apply LinearMap.ext
    intro x
    change rawTensorComponent X Y p q (rawTensorRightBoundary X Y (rawTensorInclusion X Y r s x)) =
      (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q)
        (rawTensorComponent X Y p (q + 1) (rawTensorInclusion X Y r s x))
    by_cases he : (r, s) = (p, q + 1)
    · have hr := congrArg Prod.fst he
      have hs := congrArg Prod.snd he
      change r = p at hr
      change s = q + 1 at hs
      subst r
      subst s
      rw [rawTensorComponent_right_inclusion, rawTensorComponent_inclusion]
    · rw [rawTensorComponent_right_inclusion_of_ne X Y he,
        rawTensorComponent_inclusion_of_ne X Y he, map_zero, smul_zero]
  exact LinearMap.congr_fun h c

theorem rawTensorComponent_totalBoundary (p q : ℕ) (c : RawBigradedTensorChains X Y) :
    rawTensorComponent X Y p q (rawTensorTotalBoundary X Y c) =
      TensorProduct.map (rawBoundary p) LinearMap.id (rawTensorComponent X Y (p + 1) q c) +
        (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (rawBoundary q)
          (rawTensorComponent X Y p (q + 1) c) := by
  simp only [rawTensorTotalBoundary, LinearMap.add_apply, map_add,
    rawTensorComponent_leftBoundary, rawTensorComponent_rightBoundary]

def rawTensorTotalDegree (n : ℕ) : Submodule ℚ (RawBigradedTensorChains X Y) where
  carrier := {c | ∀ p q, p + q ≠ n → rawTensorComponent X Y p q c = 0}
  zero_mem' := by intro p q _; exact map_zero _
  add_mem' := by intro c d hc hd p q hpq; rw [map_add, hc p q hpq, hd p q hpq, add_zero]
  smul_mem' := by intro r c hc p q hpq; rw [map_smul, hc p q hpq, smul_zero]

theorem rawTensorTotalBoundary_mem_totalDegree (n : ℕ)
    {c : RawBigradedTensorChains X Y} (hc : c ∈ rawTensorTotalDegree X Y (n + 1)) :
    rawTensorTotalBoundary X Y c ∈ rawTensorTotalDegree X Y n := by
  intro p q hpq
  rw [rawTensorComponent_totalBoundary, hc (p + 1) q (by omega), hc p (q + 1) (by omega),
    map_zero, map_zero, smul_zero, add_zero]

theorem rawTensorTotalBoundary_eq_zero_of_totalDegree_zero
    {c : RawBigradedTensorChains X Y} (hc : c ∈ rawTensorTotalDegree X Y 0) :
    rawTensorTotalBoundary X Y c = 0 := by
  apply DirectSum.ext_component ℚ
  rintro ⟨p, q⟩
  change rawTensorComponent X Y p q _ = 0
  rw [rawTensorComponent_totalBoundary, hc (p + 1) q (by omega), hc p (q + 1) (by omega),
    map_zero, map_zero, smul_zero, add_zero]

def rawTensorBoundary (n : ℕ) :
    rawTensorTotalDegree X Y (n + 1) →ₗ[ℚ] rawTensorTotalDegree X Y n :=
  LinearMap.codRestrict (rawTensorTotalDegree X Y n)
    ((rawTensorTotalBoundary X Y).comp (rawTensorTotalDegree X Y (n + 1)).subtype)
    (fun c => rawTensorTotalBoundary_mem_totalDegree X Y n c.property)

theorem rawTensorBoundary_squared (n : ℕ) :
    (rawTensorBoundary X Y n).comp (rawTensorBoundary X Y (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change rawTensorTotalBoundary X Y (rawTensorTotalBoundary X Y c.val) = 0
  exact LinearMap.congr_fun (rawTensorTotalBoundary_squared X Y) c.val

theorem rawAlexanderWhitney_mem_totalDegree (n : ℕ) (c : RawRationalChains (X × Y) n) :
    rawAlexanderWhitney n c ∈ rawTensorTotalDegree X Y n := by
  intro p q hpq
  have h : (rawTensorComponent X Y p q).comp (rawAlexanderWhitney n) = 0 := by
    apply Finsupp.lhom_ext
    intro σ a
    exact rawAlexanderWhitney_component_single_of_ne X Y hpq σ a
  exact LinearMap.congr_fun h c

def rawAlexanderWhitneyHomogeneous (n : ℕ) :
    RawRationalChains (X × Y) n →ₗ[ℚ] rawTensorTotalDegree X Y n :=
  LinearMap.codRestrict (rawTensorTotalDegree X Y n) (rawAlexanderWhitney n)
    (rawAlexanderWhitney_mem_totalDegree X Y n)

end BanachIsometric.SingularAW
