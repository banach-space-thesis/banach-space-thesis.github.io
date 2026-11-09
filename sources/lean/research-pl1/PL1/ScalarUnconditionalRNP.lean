import PL1.UnconditionalRNP
import PL1.ScalarDecompositionRNP
import PL1.RealSchur
import PL1.IntrinsicNonBoundedComplete

/-! # Unconditional sign bounds and RNP over real or complex scalars -/

noncomputable section
universe u v
open Filter
open scoped Topology BigOperators

namespace PL1.ScalarUnconditionalRNP

variable {K : Type*} [RCLike K]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace K E]

def difference (P : ℕ → E →L[K] E) : ℕ → E →L[K] E
  | 0 => P 0
  | n + 1 => P (n + 1) - P n

theorem hasRNP_of_schur_sign_bound [CompleteSpace E]
    (hS : HasSchurProperty K E) (P : ℕ → E →L[K] E)
    (hfinite : ∀ n, FiniteDimensional K (P n).range)
    (hnested : ∀ m n, m ≤ n → (P m).comp (P n) = P m)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (C : ℝ) (hC : 0 ≤ C)
    (htransform : ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), (ε j : K) • difference P j y‖ ≤ C * ‖y‖) :
    @HasRadonNikodymProperty.{u, v} (UnderlyingReal K E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ K E) := by
  let := NormedSpace.restrictScalars ℝ K E
  let := IsScalarTower.restrictScalars ℝ K E
  change HasRadonNikodymProperty.{u, v} E
  let Q : ℕ → E →L[ℝ] E := fun n => (P n).restrictScalars ℝ
  have hfiniteR (n : ℕ) : FiniteDimensional ℝ (Q n).range := by
    let := hfinite n
    let : FiniteDimensional ℝ (P n).range := FiniteDimensional.trans ℝ K (P n).range
    exact inferInstanceAs (FiniteDimensional ℝ (P n).range)
  have hd (j : ℕ) (y : E) : UnconditionalDecomposition.difference Q j y = difference P j y := by
    cases j <;> rfl
  refine UnconditionalRNP.hasRadonNikodymProperty_of_schur_unconditional_projections
    (hasSchurProperty_iff_real.mp hS) Q hfiniteR ?_ hstrong C hC ?_
  · intro m n hmn
    ext1 x
    exact DFunLike.congr_fun (hnested m n hmn) x
  · intro N ε y hε
    simpa only [hd, RCLike.real_smul_eq_coe_smul (K := K)] using htransform N ε y hε

theorem no_uniform_sign_bound_of_not_RNP [CompleteSpace E]
    (hS : HasSchurProperty K E)
    (hRNP : ¬ @HasRadonNikodymProperty.{u, v} (UnderlyingReal K E)
      (inferInstanceAs (NormedAddCommGroup E)) (NormedSpace.restrictScalars ℝ K E))
    (P : ℕ → E →L[K] E) (hfinite : ∀ n, FiniteDimensional K (P n).range)
    (hnested : ∀ m n, m ≤ n → (P m).comp (P n) = P m)
    (hstrong : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ε : ℕ → ℝ) (y : E),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), (ε j : K) • difference P j y‖ ≤ C * ‖y‖ := by
  rintro ⟨C, hC, htransform⟩
  exact hRNP (hasRNP_of_schur_sign_bound hS P hfinite hnested hstrong C hC htransform)

end PL1.ScalarUnconditionalRNP

namespace PL1.Noise

theorem schur_intrinsic_no_uniform_scalar_sign_bound (K : Type*) [RCLike K] :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ε : ℕ → ℝ)
      (y : (dyadicSystem K schurRates).IntrinsicSpace),
      (∀ j, ε j = 1 ∨ ε j = -1) →
        ‖∑ j ∈ Finset.range (N + 1), (ε j : K) •
          ScalarUnconditionalRNP.difference (intrinsicExpectation K schurRates) j y‖ ≤ C * ‖y‖ :=
  ScalarUnconditionalRNP.no_uniform_sign_bound_of_not_RNP
    (schurRates_intrinsic_hasSchurProperty K) (schur_intrinsic_not_RNP K)
    (intrinsicExpectation K schurRates) (intrinsicExpectation_range_finiteDimensional K schurRates)
    (intrinsicExpectation_comp_of_le K schurRates) (tendsto_intrinsicExpectation K schurRates)

end PL1.Noise
