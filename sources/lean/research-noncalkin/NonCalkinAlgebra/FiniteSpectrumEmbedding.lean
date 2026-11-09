import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Spectrum.Basic

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u v w
variable {𝕜 : Type u} [Field 𝕜] {A : Type v} {B : Type w}
  [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B] [FiniteDimensional 𝕜 A]

/-- An injective algebra map reflects invertibility when its domain is
finite-dimensional. No involution or topology on the codomain is needed. -/
theorem isUnit_map_iff_of_finiteDimensional (f : A →ₐ[𝕜] B)
    (hf : Function.Injective f) (a : A) : IsUnit (f a) ↔ IsUnit a := by
  refine ⟨?_, fun ha => ha.map f.toMonoidHom⟩
  intro hfa
  obtain ⟨c, _, hca⟩ := isUnit_iff_exists.mp hfa
  have hinj : Function.Injective (LinearMap.mulLeft 𝕜 a) := by
    intro y z hyz
    apply hf
    calc
      f y = c * (f a * f y) := by rw [← mul_assoc, hca, one_mul]
      _ = c * (f a * f z) := by
        congr 1
        simpa only [LinearMap.mulLeft_apply, map_mul] using congrArg f hyz
      _ = f z := by rw [← mul_assoc, hca, one_mul]
  obtain ⟨b, hab⟩ := LinearMap.surjective_of_injective hinj 1
  change a * b = 1 at hab
  have hba : b * a = 1 := hinj (by
    change a * (b * a) = a * 1
    rw [← mul_assoc, hab, one_mul, mul_one])
  exact isUnit_iff_exists.mpr ⟨b, hab, hba⟩

/-- Spectral permanence for finite-dimensional algebra embeddings. In
particular, it applies to matrix subalgebras in a Banach-algebra quotient. -/
theorem spectrum_map_eq_of_finiteDimensional (f : A →ₐ[𝕜] B)
    (hf : Function.Injective f) (a : A) : spectrum 𝕜 (f a) = spectrum 𝕜 a := by
  ext z
  change ¬ IsUnit (algebraMap 𝕜 B z - f a) ↔ ¬ IsUnit (algebraMap 𝕜 A z - a)
  simpa only [map_sub, AlgHom.commutes] using
    not_congr (isUnit_map_iff_of_finiteDimensional f hf (algebraMap 𝕜 A z - a))

end NonCalkinAlgebra
