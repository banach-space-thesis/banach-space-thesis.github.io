import NonCalkinAlgebra.QuotientAlgebra
import Mathlib.Algebra.Algebra.Spectrum.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u v
variable {A : Type u} [Ring A] [Algebra ℂ A]

/-- The explicit resolvent of an idempotent away from 0 and 1. -/
def idempotentResolvent (e : A) (z : ℂ) : A :=
  z⁻¹ • (1 - e) + (z - 1)⁻¹ • e

theorem idempotent_resolvent_mul (e : A) (he : e * e = e) (z : ℂ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (algebraMap ℂ A z - e) * idempotentResolvent e z = 1 := by
  have hzero : (algebraMap ℂ A z - e) * (1 - e) = z • (1 - e) := by
    calc
      (algebraMap ℂ A z - e) * (1 - e) =
          algebraMap ℂ A z * (1 - e) - e * (1 - e) := sub_mul _ _ _
      _ = algebraMap ℂ A z * (1 - e) := by
        rw [mul_sub e 1 e, mul_one, he, sub_self, sub_zero]
      _ = z • (1 - e) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hone : (algebraMap ℂ A z - e) * e = (z - 1) • e := by
    rw [sub_mul, he, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      sub_smul, one_smul]
  rw [idempotentResolvent, mul_add, mul_smul_comm, mul_smul_comm, hzero, hone,
    inv_smul_smul₀ hz0, inv_smul_smul₀ (sub_ne_zero.mpr hz1), sub_add_cancel]

theorem idempotent_mul_resolvent (e : A) (he : e * e = e) (z : ℂ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    idempotentResolvent e z * (algebraMap ℂ A z - e) = 1 := by
  have hzero : (1 - e) * (algebraMap ℂ A z - e) = z • (1 - e) := by
    calc
      (1 - e) * (algebraMap ℂ A z - e) =
          (1 - e) * algebraMap ℂ A z - (1 - e) * e := mul_sub _ _ _
      _ = (1 - e) * algebraMap ℂ A z := by
        rw [sub_mul 1 e e, one_mul, he, sub_self, sub_zero]
      _ = z • (1 - e) := by
        rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hone : e * (algebraMap ℂ A z - e) = (z - 1) • e := by
    rw [mul_sub, he, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
      sub_smul, one_smul]
  rw [idempotentResolvent, add_mul, smul_mul_assoc, smul_mul_assoc, hzero, hone,
    inv_smul_smul₀ hz0, inv_smul_smul₀ (sub_ne_zero.mpr hz1), sub_add_cancel]

theorem resolvent_idempotent (e : A) (he : e * e = e) (z : ℂ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    resolvent e z = idempotentResolvent e z := by
  let u : Aˣ :=
    { val := algebraMap ℂ A z - e
      inv := idempotentResolvent e z
      val_inv := idempotent_resolvent_mul e he z hz0 hz1
      inv_val := idempotent_mul_resolvent e he z hz0 hz1 }
  change Ring.inverse (u : A) = idempotentResolvent e z
  rw [Ring.inverse_unit]
  rfl

/-- Algebra homomorphisms preserve a resolvent whenever the original
resolvent exists. This does not assert inverse preservation at nonunits. -/
theorem algHom_map_resolvent {B : Type v} [Ring B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (a : A) (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    f (resolvent a z) = resolvent (f a) z := by
  obtain ⟨u, hu⟩ := hz
  have hmap : ((Units.map f.toMonoidHom u : Bˣ) : B) = algebraMap ℂ B z - f a := by
    change f (u : A) = _
    rw [hu, map_sub, f.commutes]
  change f (Ring.inverse (algebraMap ℂ A z - a)) =
    Ring.inverse (algebraMap ℂ B z - f a)
  rw [← hu, Ring.inverse_unit, ← hmap, Ring.inverse_unit]
  rfl

open SurveyStatements.P2
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (convention : QuotientConvention)

def operatorQuotientAlgHom : BoundedOperators X →ₐ[ℂ] OperatorQuotient X convention where
  toFun := operatorQuotientMap X convention
  map_zero' := (operatorQuotientMap X convention).map_zero
  map_one' := operatorQuotientMap_one X convention
  map_add' := (operatorQuotientMap X convention).map_add
  map_mul' := operatorQuotientMap_mul X convention
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change operatorQuotientMap X convention (c • 1) = c • 1
    rw [map_smul]
    rfl

@[simp] theorem operatorQuotientAlgHom_apply (T : BoundedOperators X) :
    operatorQuotientAlgHom X convention T = operatorQuotientMap X convention T := rfl

theorem operatorQuotientMap_resolvent (T : BoundedOperators X) (z : ℂ)
    (hz : z ∈ resolventSet ℂ T) :
    operatorQuotientMap X convention (resolvent T z) =
      resolvent (operatorQuotientMap X convention T) z :=
  algHom_map_resolvent (operatorQuotientAlgHom X convention) T z hz

end NonCalkinAlgebra
