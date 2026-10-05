import PosetsCommon.Algebra
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-! The algebraic argument of Posets Lemma 6.20, in a reusable form.
The right inverse need not be linear or continuous. -/
namespace ThesisCommon
variable {𝕜 A B : Type*} [Field 𝕜] [NonUnitalRing A] [NonUnitalRing B]
  [Module 𝕜 A] [Module 𝕜 B]

theorem multiplicative_of_section (θ : A →ₗ[𝕜] B) (I : TwoSidedIdeal A)
    (hker : ∀ x, θ x = 0 ↔ x ∈ I)
    (ρ : B → A) (hρ : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (hsection : Function.RightInverse ρ θ) :
    ∀ x y, θ (x * y) = θ x * θ y := by
  intro x y
  have hx : x - ρ (θ x) ∈ I := (hker _).mp (by rw [map_sub, hsection, sub_self])
  have hy : y - ρ (θ y) ∈ I := (hker _).mp (by rw [map_sub, hsection, sub_self])
  have h₁ : θ (x * y) = θ (ρ (θ x) * y) := by
    have h := (hker _).mpr (I.mul_mem_right _ y hx)
    simpa only [sub_mul, map_sub, sub_eq_zero] using h
  have h₂ : θ (ρ (θ x) * y) = θ (ρ (θ x) * ρ (θ y)) := by
    have h := (hker _).mpr (I.mul_mem_left (ρ (θ x)) _ hy)
    simpa only [mul_sub, map_sub, sub_eq_zero] using h
  rw [h₁, h₂, ← hρ, hsection]

end ThesisCommon
