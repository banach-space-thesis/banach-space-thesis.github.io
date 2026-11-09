import BanachIsometric.BinomialCoproduct
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# A nilpotent primitive element in characteristic zero is zero

This is an actual algebraic obstruction, with the literal comultiplication
identity as its primitive condition. Coefficient functionals and the binomial
formula give `n • x = 0` for a nonzero nilpotent candidate, a contradiction.
No graded or topological comparison is asserted: the graded even-degree and
actual singular-homotopy-to-primitive bridges remain separate obligations.
-/

noncomputable section
namespace BanachIsometric

open scoped TensorProduct BigOperators

theorem comul_pow_of_primitive
    {K A : Type*} [CommSemiring K] [Semiring A] [Bialgebra K A]
    {x : A} (hprimitive : Coalgebra.comul (R := K) x = x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x)
    (n : ℕ) :
    Coalgebra.comul (R := K) (x ^ n) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((x ^ i) ⊗ₜ[K] (x ^ (n - i))) := by
  exact binomial_coproduct_powers_of_step (Coalgebra.comul (R := K)) Bialgebra.comul_one
    (fun y => by rw [Bialgebra.comul_mul, hprimitive]) n

theorem nilpotent_eq_zero_of_primitive
    {K A : Type*} [Field K] [CharZero K] [Ring A] [Bialgebra K A] [Nontrivial A]
    {x : A} (hprimitive : Coalgebra.comul (R := K) x = x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x)
    (hx : IsNilpotent x) : x = 0 := by
  exact eq_zero_of_nilpotent_binomial_coproduct (Coalgebra.comul (R := K))
    (comul_pow_of_primitive hprimitive) hx

end BanachIsometric
