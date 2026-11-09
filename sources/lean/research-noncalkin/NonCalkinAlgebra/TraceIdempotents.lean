import NonCalkinAlgebra.TraceCoefficientSelection
import Mathlib.Analysis.Normed.Ring.Units

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Close idempotents have the same value under a bounded trace. The
intertwiner is an actual unit obtained from the geometric series. -/
theorem trace_eq_of_close_idempotents {τ : A →L[ℂ] ℂ} (hτ : IsNormalizedTrace τ)
    {e f : A} (he : e * e = e) (hf : f * f = f)
    (hclose : ‖e - f‖ * ‖e + e - 1‖ < 1) : τ e = τ f := by
  let w : A := f * e + (1 - f) * (1 - e)
  have hw : 1 - w = (e - f) * (e + e - 1) := by
    simp only [w, sub_mul, mul_sub, mul_add, one_mul, mul_one, he]
    abel
  have hwNorm : ‖1 - w‖ < 1 := by
    rw [hw]
    exact (norm_mul_le _ _).trans_lt hclose
  let u : Aˣ := Units.oneSub (1 - w) hwNorm
  have hu : (u : A) = w := by
    change 1 - (1 - w) = w
    abel
  have hfw : f * (u : A) = (u : A) * e := by
    rw [hu]
    have hf₀ : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf, sub_self]
    have he₀ : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
    calc
      f * w = f * e := by
        dsimp only [w]
        rw [mul_add, ← mul_assoc f f e, hf, ← mul_assoc f (1 - f), hf₀,
          zero_mul, add_zero]
      _ = w * e := by
        dsimp only [w]
        rw [add_mul, mul_assoc f e e, he, mul_assoc (1 - f) (1 - e) e, he₀,
          mul_zero, add_zero]
  calc
    τ e = τ ((↑u⁻¹ : A) * ((u : A) * e)) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = τ ((↑u⁻¹ : A) * (f * (u : A))) := by rw [hfw]
    _ = τ ((f * (u : A)) * (↑u⁻¹ : A)) := hτ.2 _ _
    _ = τ f := by rw [mul_assoc, Units.mul_inv, mul_one]

end NonCalkinAlgebra
