import BanachIsometric.SignedTargetRay
import BanachIsometric.SignedSimplexNullBoundary
import BanachIsometric.SimplexConeCoordinates

/-! The source chart for a coned simplex uses radius and the ordered
coordinates on its base. With the apex first, the chart determinant is
positive for positive radius. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set

def signedConeHeadAdjustment (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  signedRayJoin n
    (signedRayHead n - (signedSimplexCoordinateSum n).toContinuousLinearMap.comp
      (signedTailLinear n).toContinuousLinearMap)
    (signedTailLinear n).toContinuousLinearMap

theorem signedConeHeadAdjustment_det (n : ℕ) : (signedConeHeadAdjustment n).det = 1 := by
  have ht : (signedTailLinear n).toContinuousLinearMap (Pi.single (0 : Fin (n + 1)) 1) = 0 :=
    signedTailLinear_single_zero n
  have hh : signedRayHead n (Pi.single (0 : Fin (n + 1)) 1) = 1 := by simp [signedRayHead]
  unfold signedConeHeadAdjustment
  rw [show (signedTailLinear n).toContinuousLinearMap =
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)).comp (signedTailLinear n).toContinuousLinearMap from rfl,
    signedRayJoin_det]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, hh, ht, map_zero, sub_zero, one_mul]
  change (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)).det = 1
  exact LinearMap.det_id

def signedConeSourceChart (n : ℕ) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  signedConeHeadAdjustment n (signedTargetRay n u)

theorem signedConeSourceChart_apply (n : ℕ) (u : Fin (n + 1) → ℝ) :
    signedConeSourceChart n u = u 0 • signedSimplexBarycentric n (signedTailLinear n u) := by
  rw [signedConeSourceChart, signedTargetRay, map_smul]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change 1 - signedSimplexCoordinateSum n (signedTailLinear n u) = _
    simp
  · rfl

theorem signedConeSourceChart_hasStrictFDerivAt (n : ℕ) (u : Fin (n + 1) → ℝ) :
    HasStrictFDerivAt (signedConeSourceChart n)
      ((signedConeHeadAdjustment n).comp (signedTargetRayDerivative n u)) u := by
  let A := signedRayJoin n 0 (signedTailLinear n).toContinuousLinearMap
  let b : Fin (n + 1) → ℝ := Pi.single 0 1
  have he : (fun x : Fin (n + 1) → ℝ => Fin.cons (α := fun _ => ℝ) 1 (signedTailLinear n x)) =
      fun x => b + A x := by
    funext x i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [A, b]
    · simp [A, b]
  have hT : ContDiff ℝ 1 (signedTargetRay n) := by
    have hA : ContDiff ℝ 1
        (fun x : Fin (n + 1) → ℝ => Fin.cons (α := fun _ => ℝ) 1 (signedTailLinear n x)) := by
      rw [he]
      exact contDiff_const.add A.contDiff
    exact (signedRayHead n).contDiff.smul hA
  have hT' : HasStrictFDerivAt (signedTargetRay n) (signedTargetRayDerivative n u) u := by
    rw [← (signedTargetRay_hasFDerivAt n u).fderiv]
    exact hT.contDiffAt.hasStrictFDerivAt (by norm_num)
  exact (signedConeHeadAdjustment n).hasStrictFDerivAt.comp u hT'

theorem signedConeSourceChart_derivative_det (n : ℕ) (u : Fin (n + 1) → ℝ) :
    ((signedConeHeadAdjustment n).comp (signedTargetRayDerivative n u)).det = (u 0) ^ n := by
  change ((signedConeHeadAdjustment n).toLinearMap.comp (signedTargetRayDerivative n u).toLinearMap).det = _
  rw [LinearMap.det_comp]
  change (signedConeHeadAdjustment n).det * (signedTargetRayDerivative n u).det = _
  rw [signedConeHeadAdjustment_det, one_mul, signedTargetRayDerivative_det]

theorem signedConeSourceChart_mem (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1)
    (x : signedSimplexDomain n) : signedConeSourceChart n (Fin.cons r x.val) ∈ signedSimplexDomain (n + 1) := by
  rw [signedConeSourceChart_apply]
  change r • signedSimplexBarycentric n x.val ∈ signedSimplexDomain (n + 1)
  refine ⟨fun j => mul_nonneg hr (stdSimplex.zero_le ((signedSimplexCoordinates n).symm x) j), ?_⟩
  change (∑ j, r * signedSimplexBarycentric n x.val j) ≤ 1
  rw [← Finset.mul_sum, signedSimplexBarycentric_sum, mul_one]
  exact hr'

theorem signedConeSourceChart_radius_base (n : ℕ) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (x : signedSimplexDomain n) :
    let w := (signedSimplexCoordinates (n + 1)).symm
      ⟨signedConeSourceChart n (Fin.cons r x.val), signedConeSourceChart_mem n hr.le hr' x⟩
    ∃ h : simplexConeRadius n w = r,
      simplexConeBase n w (h.symm ▸ hr) = (signedSimplexCoordinates n).symm x := by
  dsimp only
  let w := (signedSimplexCoordinates (n + 1)).symm
    ⟨signedConeSourceChart n (Fin.cons r x.val), signedConeSourceChart_mem n hr.le hr' x⟩
  have hs : signedSimplexBarycentric (n + 1) (signedConeSourceChart n (Fin.cons r x.val)) =
      Fin.cons (1 - r) (r • signedSimplexBarycentric n x.val) := by
    rw [signedConeSourceChart_apply]
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change 1 - (∑ k, r * signedSimplexBarycentric n x.val k) = 1 - r
      rw [← Finset.mul_sum, signedSimplexBarycentric_sum, mul_one]
    · rfl
  have hR : simplexConeRadius n w = r := by
    unfold simplexConeRadius
    change 1 - signedSimplexBarycentric (n + 1) (signedConeSourceChart n (Fin.cons r x.val)) 0 = r
    rw [hs]
    simp
  refine ⟨hR, ?_⟩
  apply Subtype.ext
  funext j
  change signedSimplexBarycentric (n + 1) (signedConeSourceChart n (Fin.cons r x.val)) j.succ /
    simplexConeRadius n w = signedSimplexBarycentric n x.val j
  rw [hs, hR]
  change (r * signedSimplexBarycentric n x.val j) / r = _
  field_simp

end BanachIsometric.SingularPrism
