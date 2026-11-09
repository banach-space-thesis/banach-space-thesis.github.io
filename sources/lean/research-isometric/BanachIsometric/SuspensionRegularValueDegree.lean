import BanachIsometric.SuspensionConeDifferential
import BanachIsometric.SphereRegularValueDegree

/-! The degree of the actual suspension is computed at a regular equatorial
cone value. Fiber correspondence and determinant signs are proved from the
literal product formula; a suspension law for degree is not assumed. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped Topology NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem equatorSplit_normal_add (v : sphere (0 : V) 1) (a : ℝ) (w : (ℝ ∙ v.val)ᗮ) :
    equatorSplit v (a • v.val + (w : V)) = (a, w) := by
  change equatorSplit v ((equatorSplit v).symm (a, w)) = _
  exact (equatorSplit v).apply_symm_apply _

theorem equatorSplit_equator (v : sphere (0 : V) 1) (w : (ℝ ∙ v.val)ᗮ) :
    equatorSplit v (w : V) = (0, w) := by
  simpa only [zero_smul, zero_add] using equatorSplit_normal_add v 0 w

theorem equatorSplit_cone_of_band
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z)) (x : V) :
    equatorSplit v (unitSphereCone φ x) =
      ((equatorSplit v x).1, unitSphereCone f (equatorSplit v x).2) := by
  simpa only [coordinateMapConjugate, ContinuousLinearEquiv.symm_apply_apply] using
    congrFun (coordinateConjugate_unitSphereCone_of_band v q₀ f φ hBand) (equatorSplit v x)

theorem suspension_cone_fiber_coordinates
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    (w : (ℝ ∙ v.val)ᗮ) {x : V} (hx : unitSphereCone φ x = (w : V)) :
    ((equatorSplit v x).2 : V) = x ∧
      unitSphereCone f (equatorSplit v x).2 = w := by
  have he := congrArg (equatorSplit v) hx
  rw [equatorSplit_cone_of_band v q₀ f φ hBand, equatorSplit_equator] at he
  have hfirst : (equatorSplit v x).1 = 0 := congrArg Prod.fst he
  have hsecond : unitSphereCone f (equatorSplit v x).2 = w := congrArg Prod.snd he
  refine ⟨?_, hsecond⟩
  have h := (equatorSplit v).symm_apply_apply x
  rw [equatorSplit_symm_apply, hfirst, zero_smul, zero_add] at h
  exact h

/-- The actual cone fibers in the actual closed unit balls correspond. -/
def suspensionConeBallFiberEquiv
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    (w : (ℝ ∙ v.val)ᗮ) :
    {z : (ℝ ∙ v.val)ᗮ // z ∈ closedBall 0 1 ∧ unitSphereCone f z = w} ≃
      {x : V // x ∈ closedBall 0 1 ∧ unitSphereCone φ x = (w : V)} where
  toFun z := ⟨z.val, by
    constructor
    · simpa only [mem_closedBall, dist_zero_right] using z.property.1
    · simpa only [zero_smul, zero_add, z.property.2] using
        unitSphereCone_band_product v q₀ f φ hBand 0 z.val⟩
  invFun x := ⟨(equatorSplit v x.val).2, by
    obtain ⟨he, hf⟩ := suspension_cone_fiber_coordinates v q₀ f φ hBand w x.property.2
    refine ⟨?_, hf⟩
    rw [mem_closedBall, dist_zero_right]
    change ‖((equatorSplit v x.val).2 : V)‖ ≤ 1
    rw [he]
    simpa only [mem_closedBall, dist_zero_right] using x.property.1⟩
  left_inv z := by
    apply Subtype.ext
    change (equatorSplit v (z.val : V)).2 = z.val
    rw [equatorSplit_equator]
  right_inv x := by
    apply Subtype.ext
    exact (suspension_cone_fiber_coordinates v q₀ f φ hBand w x.property.2).1

theorem sphereSignedDegree_suspension_eq_natCard_of_positive_regular_value
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    {C : ℝ≥0} (hf : LipschitzWith C f)
    (w : (ℝ ∙ v.val)ᗮ) (hw : ‖w‖ < 1)
    (hdiff : ∀ z ∈ closedBall (0 : (ℝ ∙ v.val)ᗮ) 1, unitSphereCone f z = w →
      DifferentiableAt ℝ (unitSphereCone f) z)
    (hpos : ∀ z ∈ closedBall (0 : (ℝ ∙ v.val)ᗮ) 1, unitSphereCone f z = w →
      0 < (fderiv ℝ (unitSphereCone f) z).det) :
    sphereSignedDegree e φ =
      (Nat.card {z : (ℝ ∙ v.val)ᗮ // z ∈ closedBall 0 1 ∧ unitSphereCone f z = w} : ℤ) := by
  obtain ⟨L, hL⟩ := exists_lipschitz_sphereMap_of_band v q₀ f φ hBand hf
  have hreg (x : V) (hx : x ∈ closedBall (0 : V) 1)
      (hxc : unitSphereCone φ x = (w : V)) :
      DifferentiableAt ℝ (unitSphereCone φ) x ∧
        0 < (fderiv ℝ (unitSphereCone φ) x).det := by
    obtain ⟨he, hpre⟩ := suspension_cone_fiber_coordinates v q₀ f φ hBand w hxc
    have hb : (equatorSplit v x).2 ∈ closedBall (0 : (ℝ ∙ v.val)ᗮ) 1 := by
      rw [mem_closedBall, dist_zero_right]
      change ‖((equatorSplit v x).2 : V)‖ ≤ 1
      rw [he]
      simpa only [mem_closedBall, dist_zero_right] using hx
    have hd := hdiff _ hb hpre
    constructor
    · have h := differentiableAt_unitSphereCone_of_band v q₀ f φ hBand 0 _ hd
      simpa only [zero_smul, zero_add, he] using h
    · have h := det_fderiv_unitSphereCone_of_band v q₀ f φ hBand 0 _ hd
      simp only [zero_smul, zero_add, he] at h
      rw [h]
      exact hpos _ hb hpre
  rw [sphereSignedDegree_eq_natCard_of_positive_regular_value e hL hw
    (fun x hx hxc => (hreg x hx hxc).1) (fun x hx hxc => (hreg x hx hxc).2)]
  exact congrArg (fun k : ℕ => (k : ℤ))
    (Nat.card_congr (suspensionConeBallFiberEquiv v q₀ f φ hBand w)).symm

theorem sphereSignedDegree_suspension_eq_of_positive_regular_value
    {n m : ℕ} [NeZero n] [NeZero m] (e : V ≃L[ℝ] PiolaSpace n)
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (eW : (ℝ ∙ v.val)ᗮ ≃L[ℝ] PiolaSpace m)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    {C : ℝ≥0} (hf : LipschitzWith C f)
    (w : (ℝ ∙ v.val)ᗮ) (hw : ‖w‖ < 1)
    (hdiff : ∀ z ∈ closedBall (0 : (ℝ ∙ v.val)ᗮ) 1, unitSphereCone f z = w →
      DifferentiableAt ℝ (unitSphereCone f) z)
    (hpos : ∀ z ∈ closedBall (0 : (ℝ ∙ v.val)ᗮ) 1, unitSphereCone f z = w →
      0 < (fderiv ℝ (unitSphereCone f) z).det) :
    sphereSignedDegree e φ = sphereSignedDegree eW f := by
  rw [sphereSignedDegree_suspension_eq_natCard_of_positive_regular_value e v q₀ f φ hBand hf w hw
    hdiff hpos, sphereSignedDegree_eq_natCard_of_positive_regular_value eW hf hw hdiff hpos]

end BanachIsometric
