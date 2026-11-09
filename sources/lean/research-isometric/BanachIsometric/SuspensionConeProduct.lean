import BanachIsometric.SuspensionBand
import BanachIsometric.UnitSphereConeFibers
import BanachIsometric.SignedCoordinateTransport
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The cone of the actual conewise suspension is the identity on its normal
line and the original cone on its orthogonal equator. The product below has
its existing product norm; only a continuous linear equivalence is asserted. -/

noncomputable section
namespace BanachIsometric
open Set Metric NormedSpace
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem equator_normal_norm_sq (v : sphere (0 : V) 1) (a : ℝ)
    (w : (ℝ ∙ v.val)ᗮ) :
    ‖a • v.val + (w : V)‖ ^ 2 = a ^ 2 + ‖w‖ ^ 2 := by
  have hvw : inner ℝ v.val (w : V) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  have hwv : inner ℝ (w : V) v.val = 0 := by rw [real_inner_comm, hvw]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hvw, hwv, mul_zero, zero_add, add_zero,
    real_inner_self_eq_norm_sq]
  rw [norm_smul, norm_eq_of_mem_sphere v, mul_one, Real.norm_eq_abs, sq_abs]
  rfl

/-- Actual orthogonal coordinates, with the unchanged norm on each factor. -/
def equatorSplit [FiniteDimensional ℝ V] (v : sphere (0 : V) 1) :
    V ≃L[ℝ] (ℝ × (ℝ ∙ v.val)ᗮ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (inner ℝ v.val x, ⟨x - (inner ℝ v.val x) • v.val, by
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
          norm_eq_of_mem_sphere v]
        norm_num⟩)
      invFun := fun p => p.1 • v.val + (p.2 : V)
      left_inv := by intro x; dsimp; module
      right_inv := by
        intro p
        have hw : inner ℝ v.val (p.2 : V) = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property
        have hvv : inner ℝ v.val v.val = 1 := by
          rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]; norm_num
        apply Prod.ext
        · dsimp; rw [inner_add_right, real_inner_smul_right, hvv, hw]; ring
        · apply Subtype.ext
          dsimp
          rw [inner_add_right, real_inner_smul_right, hvv, hw]
          module
      map_add' := by
        intro x y
        apply Prod.ext
        · exact inner_add_right _ _ _
        · apply Subtype.ext; dsimp; rw [inner_add_right]; module
      map_smul' := by
        intro c x
        apply Prod.ext
        · exact real_inner_smul_right _ _ _
        · apply Subtype.ext; dsimp; rw [real_inner_smul_right]; module }

@[simp] theorem equatorSplit_symm_apply [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (p : ℝ × (ℝ ∙ v.val)ᗮ) :
    (equatorSplit v).symm p = p.1 • v.val + (p.2 : V) := rfl

/-- Literal product formula. The band action is discharged for the actual
conewise suspension by `suspension_equatorBand` below. -/
theorem unitSphereCone_band_product
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) = equatorBand v (a, f z))
    (a : ℝ) (w : (ℝ ∙ v.val)ᗮ) :
    unitSphereCone φ (a • v.val + (w : V)) =
      a • v.val + ((unitSphereCone f w : (ℝ ∙ v.val)ᗮ) : V) := by
  classical
  let z : EquatorSphere v := if hw : w = 0 then q₀ else coneDirection w hw
  have hwz : w = ‖w‖ • z.val := by
    by_cases hw : w = 0
    · simp [z, hw]
    · simp only [z, dif_neg hw, coneDirection]
      exact (norm_smul_normalize w).symm
  have hcone : unitSphereCone f w = ‖w‖ • (f z).val := by
    conv_lhs => rw [hwz]
    rw [unitSphereCone, coneExtension_smul_nonneg _ (norm_nonneg _), coneExtension_unit]
  let R : ℝ := ‖a • v.val + (w : V)‖
  have hsq : R ^ 2 = a ^ 2 + ‖w‖ ^ 2 := equator_normal_norm_sq v a w
  by_cases hR : R = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg ‖w‖]
    have hw : w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w, sq_nonneg a])
    simp [ha, hw, unitSphereCone]
  have hRpos : 0 < R := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hR)
  have hheight : -1 ≤ a / R ∧ a / R ≤ 1 := by
    constructor
    · rw [le_div_iff₀ hRpos]; nlinarith [sq_nonneg ‖w‖]
    · rw [div_le_iff₀ hRpos]; nlinarith [sq_nonneg ‖w‖]
  let b : Icc (-1 : ℝ) 1 := ⟨a / R, hheight⟩
  have hrad : 0 ≤ 1 - (a / R) ^ 2 := by nlinarith [hheight.1, hheight.2]
  have hsqrt : Real.sqrt (1 - (a / R) ^ 2) = ‖w‖ / R := by
    have hratio : 0 ≤ ‖w‖ / R := div_nonneg (norm_nonneg _) hRpos.le
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hratio).mp
    rw [Real.sq_sqrt hrad]
    field_simp
    nlinarith [hsq]
  have hrepr (t : EquatorSphere v) :
      R • (equatorBand v (b, t)).val = a • v.val + ‖w‖ • t.val.val := by
    change R • ((a / R) • v.val + Real.sqrt (1 - (a / R) ^ 2) • t.val.val) = _
    rw [hsqrt, smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> field_simp
  have hx : a • v.val + (w : V) = R • (equatorBand v (b, z)).val := by
    rw [hrepr]
    congr 1
    exact congrArg (fun t : (ℝ ∙ v.val)ᗮ => (t : V)) hwz
  rw [hx, unitSphereCone, coneExtension_smul_nonneg _ hRpos.le, coneExtension_unit, hBand]
  rw [hrepr, hcone]
  rfl

theorem suspension_unitSphereCone_product [FiniteDimensional ℝ V]
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (f : C(EquatorSphere v, EquatorSphere v))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hN : ∀ x : closedHemisphere v, φ x.val = (hemisphereMap v q₀ f x).val)
    (hS : ∀ x : closedHemisphere (-v), φ x.val =
      (hemisphereMap (-v) (equatorOppositePole v q₀) (oppositeEquatorMap v f) x).val)
    (a : ℝ) (w : (ℝ ∙ v.val)ᗮ) :
    unitSphereCone φ (a • v.val + (w : V)) =
      a • v.val + ((unitSphereCone f w : (ℝ ∙ v.val)ᗮ) : V) :=
  unitSphereCone_band_product v q₀ f φ (suspension_equatorBand v q₀ f φ hN hS) a w

end BanachIsometric
