import BanachIsometric.IsometricSphereRegularValue
import BanachIsometric.SuspensionRegularValueDegree

/-! The actual suspended map is evaluated using a positive regular anchor
given in genuine isometric coordinates on the equator. This connects the
standard repetition map's concrete derivatives and fibers to the original
ambient sphere, without replacing the isometry by an arbitrary homeomorphism. -/

noncomputable section
namespace BanachIsometric
open Set Metric
open scoped NNReal

variable {V U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup U] [NormedSpace ℝ U]

theorem sphereSignedDegree_suspension_isometric_eq_natCard
    {n : ℕ} [NeZero n] (e : V ≃L[ℝ] PiolaSpace n)
    (v : sphere (0 : V) 1) (q₀ : EquatorSphere v)
    (L : (ℝ ∙ v.val)ᗮ ≃ₗᵢ[ℝ] U)
    (f : C(sphere (0 : U) 1, sphere (0 : U) 1))
    (φ : C(sphere (0 : V) 1, sphere (0 : V) 1))
    (hBand : ∀ (a : Icc (-1 : ℝ) 1) (z : EquatorSphere v),
      φ (equatorBand v (a, z)) =
        equatorBand v (a, isometricSphereConjugateContinuous L f z))
    {C : ℝ≥0} (hf : LipschitzWith C f) (y : U) (hy : ‖y‖ < 1)
    (hdiff : ∀ z ∈ closedBall (0 : U) 1, unitSphereCone f z = y →
      DifferentiableAt ℝ (unitSphereCone f) z)
    (hpos : ∀ z ∈ closedBall (0 : U) 1, unitSphereCone f z = y →
      0 < (fderiv ℝ (unitSphereCone f) z).det) :
    sphereSignedDegree e φ =
      (Nat.card {z : U // z ∈ closedBall 0 1 ∧ unitSphereCone f z = y} : ℤ) := by
  have hG : LipschitzWith C (isometricSphereConjugateContinuous L f) :=
    lipschitzWith_isometricSphereConjugate L hf
  have hreg := positive_regular_anchor_isometricSphereConjugate L f y hdiff hpos
  have hyW : ‖L.symm y‖ < 1 := by rwa [L.symm.norm_map]
  rw [sphereSignedDegree_suspension_eq_natCard_of_positive_regular_value e v q₀
    (isometricSphereConjugateContinuous L f) φ hBand hG (L.symm y) hyW
    (fun x hx hxy => (hreg x hx hxy).1) (fun x hx hxy => (hreg x hx hxy).2)]
  exact congrArg (fun k : ℕ => (k : ℤ)) (card_isometricSphereConeBallFiber L f y)

end BanachIsometric
