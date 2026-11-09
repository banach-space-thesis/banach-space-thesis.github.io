import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp

/-! A linear obstruction controls finiteness of a quotient when the image
of its kernel is contained in a finite-dimensional subspace. -/

noncomputable section
namespace BanachIsometric

theorem finiteDimensional_of_surjective_with_obstruction
    {A B C : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    [AddCommGroup C] [Module ℚ C] [FiniteDimensional ℚ C]
    (p : A →ₗ[ℚ] B) (d : A →ₗ[ℚ] C) (hp : Function.Surjective p)
    (S : Submodule ℚ B) [FiniteDimensional ℚ S]
    (hkernel : ∀ a, d a = 0 → p a ∈ S) :
    FiniteDimensional ℚ B := by
  have h : LinearMap.ker d ≤ LinearMap.ker (S.mkQ.comp p) := by
    intro a ha
    change (Submodule.Quotient.mk (p a) : B ⧸ S) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hkernel a ha)
  let f := (LinearMap.ker d).liftQ (S.mkQ.comp p) h
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨b, rfl⟩ := S.mkQ_surjective q
    obtain ⟨a, rfl⟩ := hp b
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  letI : FiniteDimensional ℚ (A ⧸ LinearMap.ker d) :=
    FiniteDimensional.of_injective d.quotKerEquivRange.toLinearMap d.quotKerEquivRange.injective
  letI : FiniteDimensional ℚ (B ⧸ S) := FiniteDimensional.of_surjective f hf
  exact Module.Finite.of_submodule_quotient S

end BanachIsometric
