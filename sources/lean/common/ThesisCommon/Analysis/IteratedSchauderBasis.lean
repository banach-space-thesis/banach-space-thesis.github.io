import ThesisCommon.Analysis.IteratedSchauderSum
import ThesisCommon.Analysis.SchauderSumBasis
import Mathlib.Data.Nat.Pairing

/-! A proved one-unconditional Schauder basis for the actual finite
iteration, together with its exact identification with the terminal vectors
and coordinates. The enumeration uses iterated natural-number pairing.
-/
noncomputable section
universe u v
namespace ThesisCommon

/-- A concrete bijective enumeration of nonempty finite tuples. -/
def natTupleEnumeration : (n : ℕ) → ℕ ≃ (Fin (n + 1) → ℕ)
  | 0 =>
      { toFun := fun k _ => k
        invFun := fun t => t 0
        left_inv := fun _ => rfl
        right_inv := fun t => by funext i; exact congrArg t (Fin.ext (by omega)) }
  | n + 1 =>
      { toFun := fun k => Fin.cons (Nat.unpair k).1
          (natTupleEnumeration n (Nat.unpair k).2)
        invFun := fun t => Nat.pair (t 0) ((natTupleEnumeration n).symm (Fin.tail t))
        left_inv := by intro k; simp
        right_inv := by intro t; simp }

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The product Schauder basis, with its proved one-unconditional inequality. -/
def iteratedUnconditionalBasis (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) :
    {b : NormalizedSchauderBasis 𝕜 (iteratedSchauderSum first tail).Carrier //
      b.IsOneUnconditional} :=
  match tail with
  | [] => ⟨first.basis, first.oneUnconditional⟩
  | next :: rest =>
      let inner := iteratedUnconditionalBasis next rest
      ⟨SchauderSum.productBasis (b := first.basis) (hb := first.oneUnconditional)
          inner.val inner.property Nat.pairEquiv.symm,
        SchauderSum.productBasis_oneUnconditional inner.val inner.property Nat.pairEquiv.symm⟩

theorem iteratedUnconditionalBasis_vector (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) (k : ℕ) :
    (iteratedUnconditionalBasis first tail).val.vector k =
      iteratedBasisVector first tail (natTupleEnumeration tail.length k) := by
  induction tail generalizing first k with
  | nil => rfl
  | cons next rest ih =>
    change SchauderSum.single (b := first.basis) (hb := first.oneUnconditional)
      (Nat.unpair k).1 ((iteratedUnconditionalBasis next rest).val.vector (Nat.unpair k).2) = _
    rw [ih]
    rfl

theorem iteratedUnconditionalBasis_coord (first : BasisSumFactor.{u,v} 𝕜)
    (tail : List (BasisSumFactor.{u,v} 𝕜)) (k : ℕ) :
    (iteratedUnconditionalBasis first tail).val.coord k =
      iteratedBasisCoordinate first tail (natTupleEnumeration tail.length k) := by
  induction tail generalizing first k with
  | nil => rfl
  | cons next rest ih =>
    change ((iteratedUnconditionalBasis next rest).val.coord (Nat.unpair k).2).comp
      (SchauderSum.coordinate (b := first.basis) (hb := first.oneUnconditional)
        (Y := (iteratedSchauderSum next rest).Carrier) (Nat.unpair k).1) = _
    rw [ih]
    rfl

end ThesisCommon
