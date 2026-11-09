import AutomaticContinuity.Statement
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false

namespace AutomaticContinuity

universe u

/-- Corollary B of the manuscript. The character is algebraic, the algebra may
be nonunital, and the seminorm estimate holds for every increasing defining
sequence. The sequence is indexed from zero; shifting the index gives the
manuscript's indexing from one. -/
def CorollaryBStatement : Prop :=
  ∀ (A : Type u) [NonUnitalCommRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    [TopologicalSpace.MetrizableSpace A],
    IsLocallyMultiplicativelyConvex A →
    ∀ χ : Character A, Continuous (fun a => χ.val a) ∧
      ∀ p : ℕ → Seminorm ℂ A, Monotone p →
        (∀ n, IsSubmultiplicative A (p n)) → WithSeminorms p →
        ∃ n : ℕ, ∀ a : A, ‖χ.val a‖ ≤ p n a

end AutomaticContinuity
