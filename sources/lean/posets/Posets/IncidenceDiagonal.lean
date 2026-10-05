import Posets.QuotientStatements

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P] [LocallyFiniteOrder P]

def incidenceDiagonal (a : P → 𝕜) : IncidenceAlgebra 𝕜 P where
  toFun s t := if s = t then a s else 0
  eq_zero_of_not_le' := by
    intro s t hst
    exact if_neg (fun h : s = t => hst h.le)

omit [LocallyFiniteOrder P] in
theorem incidenceDiagonal_apply (a : P → 𝕜) (s t : P) :
    incidenceDiagonal a s t = if s = t then a s else 0 := rfl

theorem incidenceDiagonal_mul (a : P → 𝕜) (f : IncidenceAlgebra 𝕜 P) (s t : P) :
    (incidenceDiagonal a * f) s t = a s * f s t := by
  by_cases hst : s ≤ t
  · simp [IncidenceAlgebra.mul_apply, incidenceDiagonal_apply, ite_mul, hst]
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hst,
      IncidenceAlgebra.apply_eq_zero_of_not_le hst, mul_zero]

/-- The diagonal point idempotents are eigenvectors for diagonal multiplication. -/
theorem incidenceDiagonal_mul_point (a : P → 𝕜) (p : P) :
    incidenceDiagonal a * incidenceDiagonal (Pi.single p 1) =
      a p • incidenceDiagonal (Pi.single p 1) := by
  apply IncidenceAlgebra.ext
  intro s t _
  rw [incidenceDiagonal_mul, IncidenceAlgebra.constSMul_apply, incidenceDiagonal_apply]
  by_cases hsp : s = p
  · subst s; rfl
  · simp [Pi.single_eq_of_ne hsp]

omit [LocallyFiniteOrder P] in
theorem incidenceDiagonal_point_ne_zero (p : P) :
    incidenceDiagonal (Pi.single p (1 : 𝕜)) ≠ 0 := by
  intro h
  have he := congrArg (fun f : IncidenceAlgebra 𝕜 P => f p p) h
  simp [incidenceDiagonal_apply, IncidenceAlgebra.zero_apply] at he

end Posets
