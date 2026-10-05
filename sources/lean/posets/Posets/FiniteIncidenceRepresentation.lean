import Posets.QuotientStatements
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The finite matrix representation used in Propositions 6.6 and 6.8. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open scoped BigOperators
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type} [PartialOrder P]
  [LocallyFiniteOrder P] [Fintype P]

theorem incidence_mul_univ (f g : IncidenceAlgebra 𝕜 P) (s t : P) :
    (f * g) s t = ∑ r : P, f s r * g r t := by
  classical
  rw [IncidenceAlgebra.mul_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  by_cases hsr : s ≤ r
  · have hrt : ¬ r ≤ t := fun h => hr (Finset.mem_Icc.mpr ⟨hsr, h⟩)
    rw [IncidenceAlgebra.apply_eq_zero_of_not_le hrt g, mul_zero]
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hsr f, zero_mul]

def finiteIncidenceLinear (f : IncidenceAlgebra 𝕜 P) : (P → 𝕜) →ₗ[𝕜] (P → 𝕜) where
  toFun x s := ∑ t, f s t * x t
  map_add' := by intro x y; funext s; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    funext s
    simp [Finset.mul_sum, mul_left_comm]

def finiteIncidenceOperator (f : IncidenceAlgebra 𝕜 P) : (P → 𝕜) →L[𝕜] (P → 𝕜) :=
  (finiteIncidenceLinear f).toContinuousLinearMap

omit [LocallyFiniteOrder P] in
theorem finiteIncidenceOperator_apply (f : IncidenceAlgebra 𝕜 P) (x : P → 𝕜) (s : P) :
    finiteIncidenceOperator f x s = ∑ t, f s t * x t := rfl

omit [LocallyFiniteOrder P] in
theorem finiteIncidenceOperator_single (f : IncidenceAlgebra 𝕜 P) (s t : P) :
    finiteIncidenceOperator f (Pi.single t 1) s = f s t := by
  classical
  simp [finiteIncidenceOperator_apply, Pi.single_apply]

omit [LocallyFiniteOrder P] in
theorem finiteIncidenceOperator_injective :
    Function.Injective (finiteIncidenceOperator (𝕜 := 𝕜) (P := P)) := by
  intro f g h
  apply IncidenceAlgebra.ext
  intro s t _
  simpa only [finiteIncidenceOperator_single] using
    congrArg (fun T : (P → 𝕜) →L[𝕜] (P → 𝕜) => T (Pi.single t 1) s) h

omit [LocallyFiniteOrder P] in
theorem finiteIncidenceOperator_add (f g : IncidenceAlgebra 𝕜 P) :
    finiteIncidenceOperator (f + g) = finiteIncidenceOperator f + finiteIncidenceOperator g := by
  ext x s
  simp [finiteIncidenceOperator_apply, IncidenceAlgebra.add_apply, add_mul, Finset.sum_add_distrib]

theorem finiteIncidenceOperator_smul (a : 𝕜) (f : IncidenceAlgebra 𝕜 P) :
    finiteIncidenceOperator (a • f) = a • finiteIncidenceOperator f := by
  ext x s
  simp [finiteIncidenceOperator_apply, IncidenceAlgebra.constSMul_apply, Finset.mul_sum, mul_assoc]

theorem finiteIncidenceOperator_mul (f g : IncidenceAlgebra 𝕜 P) :
    finiteIncidenceOperator (f * g) = finiteIncidenceOperator f * finiteIncidenceOperator g := by
  ext x s
  change (∑ t, (f * g) s t * x t) = ∑ r, f s r * ∑ t, g r t * x t
  simp_rw [incidence_mul_univ, Finset.sum_mul, mul_assoc, Finset.mul_sum]
  exact Finset.sum_comm

omit [LocallyFiniteOrder P] in
theorem finiteIncidenceOperator_zero :
    finiteIncidenceOperator (0 : IncidenceAlgebra 𝕜 P) = 0 := by
  ext x s
  simp [finiteIncidenceOperator_apply, IncidenceAlgebra.zero_apply]

/-- Pull back the genuine operator norm along the faithful finite representation. -/
theorem finite_incidence_normable : AlgebraNormExists 𝕜 (IncidenceAlgebra 𝕜 P) := by
  refine ⟨fun f => ‖finiteIncidenceOperator f‖, fun f => norm_nonneg _, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [norm_eq_zero, ← finiteIncidenceOperator_zero]
    exact finiteIncidenceOperator_injective.eq_iff
  · intro f g
    dsimp only
    rw [finiteIncidenceOperator_add]
    exact norm_add_le _ _
  · intro a f
    dsimp only
    rw [finiteIncidenceOperator_smul, norm_smul]
  · intro f g
    dsimp only
    rw [finiteIncidenceOperator_mul]
    exact norm_mul_le _ _

end Posets
