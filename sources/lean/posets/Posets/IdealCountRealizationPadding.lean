import Posets.ProductIdealFiniteActive
import Posets.SemisimpleQuotient

/-! Zero padding of a finite family of admissible Banach algebras. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
open ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (F : Fin n → Type) [∀ i, NormedRing (F i)] [∀ i, NormedAlgebra 𝕜 (F i)]

def finiteAlgebraOption : Option (Fin n) → Type
  | none => fullOperatorFactor 𝕜 0
  | some i => F i

instance finiteAlgebraOption_normedRing (i : Option (Fin n)) :
    NormedRing (finiteAlgebraOption (𝕜 := 𝕜) F i) := by
  cases i <;> dsimp [finiteAlgebraOption] <;> infer_instance

instance finiteAlgebraOption_normedAlgebra (i : Option (Fin n)) :
    NormedAlgebra 𝕜 (finiteAlgebraOption (𝕜 := 𝕜) F i) := by
  cases i <;> dsimp [finiteAlgebraOption] <;> infer_instance

instance finiteAlgebraOption_complete [∀ i, CompleteSpace (F i)] (i : Option (Fin n)) :
    CompleteSpace (finiteAlgebraOption (𝕜 := 𝕜) F i) := by
  cases i <;> dsimp [finiteAlgebraOption] <;> infer_instance

abbrev paddedFiniteAlgebra (m : ℕ) : Type :=
  finiteAlgebraOption (𝕜 := 𝕜) F (if h : m < n then some ⟨m, h⟩ else none)

theorem paddedFiniteAlgebra_admissible (hF : ∀ i, AdmissibleAlgebra 𝕜 (F i)) (m : ℕ) :
    AdmissibleAlgebra 𝕜 (paddedFiniteAlgebra (𝕜 := 𝕜) F m) := by
  by_cases h : m < n
  · dsimp only [paddedFiniteAlgebra]
    rw [dif_pos h]
    exact hF ⟨m, h⟩
  · dsimp only [paddedFiniteAlgebra]
    rw [dif_neg h]
    exact admissible_fullOperatorFactor 𝕜 0

theorem paddedFiniteAlgebra_trivial_tail (m : ℕ) (hm : n ≤ m) :
    Subsingleton (paddedFiniteAlgebra (𝕜 := 𝕜) F m) := by
  unfold paddedFiniteAlgebra
  rw [dif_neg (not_lt.mpr hm)]
  exact inferInstanceAs (Subsingleton (fullOperatorFactor 𝕜 0))

def paddedFiniteAlgebra_coordinate_data (i : Fin n) :
    {e : paddedFiniteAlgebra (𝕜 := 𝕜) F i.val ≃ₗᵢ[𝕜] F i //
      ∀ a b, e (a * b) = e a * e b} := by
  dsimp only [paddedFiniteAlgebra]
  rw [dif_pos i.isLt]
  exact ⟨LinearIsometryEquiv.refl 𝕜 (F i), fun _ _ => rfl⟩

def paddedFiniteAlgebra_coordinate (i : Fin n) :
    paddedFiniteAlgebra (𝕜 := 𝕜) F i.val ≃ₗᵢ[𝕜] F i :=
  (paddedFiniteAlgebra_coordinate_data F i).val

theorem paddedFiniteAlgebra_coordinate_mul (i : Fin n)
    (a b : paddedFiniteAlgebra (𝕜 := 𝕜) F i.val) :
    paddedFiniteAlgebra_coordinate F i (a * b) =
      paddedFiniteAlgebra_coordinate F i a * paddedFiniteAlgebra_coordinate F i b := by
  exact (paddedFiniteAlgebra_coordinate_data F i).property a b

def paddedFiniteAlgebra_closedIdealEquiv :
    ClosedIdeal 𝕜 (NormedProduct (paddedFiniteAlgebra (𝕜 := 𝕜) F)) ≃
      ClosedIdeal 𝕜 (∀ i, F i) :=
  (normedProductPrefixClosedIdealOrderIso (𝕜 := 𝕜)
    (paddedFiniteAlgebra (𝕜 := 𝕜) F) n (paddedFiniteAlgebra_trivial_tail F)).toEquiv.trans
      ((Equiv.piCongrRight (fun i =>
        (closedIdealLinearEquivOrderIso (paddedFiniteAlgebra_coordinate F i).toContinuousLinearEquiv
          (paddedFiniteAlgebra_coordinate_mul F i)).toEquiv)).trans
            (productClosedIdealOrderIso (𝕜 := 𝕜) F).toEquiv.symm)

def paddedFiniteAlgebra_maximalClosedIdealEquiv :
    MaximalClosedIdeals 𝕜 (NormedProduct (paddedFiniteAlgebra (𝕜 := 𝕜) F)) ≃
      MaximalClosedIdeals 𝕜 (∀ i, F i) :=
  (normedProductPrefixMaximalClosedIdealEquiv (𝕜 := 𝕜)
    (paddedFiniteAlgebra (𝕜 := 𝕜) F) n (paddedFiniteAlgebra_trivial_tail F)).trans
      ((Equiv.sigmaCongrRight (fun i =>
        maximalClosedIdealLinearEquiv (paddedFiniteAlgebra_coordinate F i).toContinuousLinearEquiv
          (paddedFiniteAlgebra_coordinate_mul F i))).trans
            (productMaximalClosedIdealEquiv (𝕜 := 𝕜) F).symm)

end Posets
