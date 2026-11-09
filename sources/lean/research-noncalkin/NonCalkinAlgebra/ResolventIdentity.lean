import NonCalkinAlgebra.IdempotentResolvent

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
variable {A : Type u} [Ring A] [Algebra ℂ A]

/-- The second resolvent identity, with the product order fixed explicitly. -/
theorem resolvent_mul_identity (a : A) (z w : ℂ)
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) (hzw : z ≠ w) :
    resolvent a z * resolvent a w =
      (z - w)⁻¹ • (resolvent a w - resolvent a z) := by
  have hdiff : (algebraMap ℂ A z - a) - (algebraMap ℂ A w - a) = (z - w) • (1 : A) := by
    calc
      (algebraMap ℂ A z - a) - (algebraMap ℂ A w - a) =
          algebraMap ℂ A z - algebraMap ℂ A w := by abel
      _ = (z - w) • (1 : A) := by rw [← map_sub, Algebra.algebraMap_eq_smul_one]
  have hzi : resolvent a z * (algebraMap ℂ A z - a) = 1 := Ring.inverse_mul_cancel _ hz
  have hwi : (algebraMap ℂ A w - a) * resolvent a w = 1 := Ring.mul_inverse_cancel _ hw
  have hprod : (z - w) • (resolvent a z * resolvent a w) = resolvent a w - resolvent a z := by
    calc
      (z - w) • (resolvent a z * resolvent a w) =
          resolvent a z * ((z - w) • (1 : A)) * resolvent a w := by
        simp only [mul_smul_comm, mul_one, smul_mul_assoc]
      _ = resolvent a z * ((algebraMap ℂ A z - a) - (algebraMap ℂ A w - a)) *
          resolvent a w := by rw [hdiff]
      _ = (resolvent a z * (algebraMap ℂ A z - a)) * resolvent a w -
          resolvent a z * ((algebraMap ℂ A w - a) * resolvent a w) := by
        rw [mul_sub, sub_mul]
        simp only [mul_assoc]
      _ = resolvent a w - resolvent a z := by rw [hzi, hwi, one_mul, mul_one]
  calc
    resolvent a z * resolvent a w =
        (z - w)⁻¹ • ((z - w) • (resolvent a z * resolvent a w)) :=
      (inv_smul_smul₀ (sub_ne_zero.mpr hzw) _).symm
    _ = (z - w)⁻¹ • (resolvent a w - resolvent a z) := congrArg (fun x : A => (z - w)⁻¹ • x) hprod

end NonCalkinAlgebra
