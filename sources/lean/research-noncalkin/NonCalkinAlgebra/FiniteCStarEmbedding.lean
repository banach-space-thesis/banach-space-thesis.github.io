import NonCalkinAlgebra.FiniteSpectrumEmbedding
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v
variable {A : Type u} {B : Type v}
  [CStarAlgebra A] [FiniteDimensional ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]

/-- An injective algebra map on a finite-dimensional C*-algebra cannot
decrease the norm of a self-adjoint element, even if its codomain is only
a Banach algebra. This follows from finite-dimensional spectral permanence. -/
theorem norm_le_map_of_finiteDimensional_selfAdjoint (f : A →ₐ[ℂ] B)
    (hf : Function.Injective f) {a : A} (ha : IsSelfAdjoint a) : ‖a‖ ≤ ‖f a‖ := by
  have hspec : spectralRadius ℂ (f a) = spectralRadius ℂ a := by
    simp only [spectralRadius, spectrum_map_eq_of_finiteDimensional f hf a]
  have h := spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) (f a)
  rw [hspec, ha.spectralRadius_eq_nnnorm] at h
  exact_mod_cast h

/-- An injective *-algebra map on a finite-dimensional C*-algebra cannot
decrease any norm when the target involution is isometric. The target is
not assumed to satisfy the C*-identity. -/
theorem norm_le_starAlgHom_of_finiteDimensional [StarRing B] [NormedStarGroup B]
    (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f) (a : A) : ‖a‖ ≤ ‖f a‖ := by
  have h := norm_le_map_of_finiteDimensional_selfAdjoint f.toAlgHom hf
    (IsSelfAdjoint.star_mul_self a)
  have hs : ‖a‖ * ‖a‖ ≤ ‖f a‖ * ‖f a‖ := by
    calc
      ‖a‖ * ‖a‖ = ‖star a * a‖ := (CStarRing.norm_star_mul_self (x := a)).symm
      _ ≤ ‖f (star a * a)‖ := h
      _ = ‖star (f a) * f a‖ := by rw [map_mul, map_star]
      _ ≤ ‖star (f a)‖ * ‖f a‖ := norm_mul_le _ _
      _ = ‖f a‖ * ‖f a‖ := by rw [norm_star]
  nlinarith [norm_nonneg a, norm_nonneg (f a)]

end NonCalkinAlgebra
