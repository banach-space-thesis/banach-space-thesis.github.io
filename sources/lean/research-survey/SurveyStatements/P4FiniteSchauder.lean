import SurveyStatements.P4Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.BigOperators.Fin

/-! Finite algebraic bases satisfy the actual ordered Schauder definition. -/

noncomputable section
set_option autoImplicit false

open Set Finset Filter Topology Module

namespace SurveyStatements.P4

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {N : ℕ}

def finiteBasisSequence (b : Basis (Fin N) 𝕜 E) : Set.Iio N → E :=
  fun i => b ⟨i.val, i.property⟩

lemma schauderPartialSum_finiteBasis (b : Basis (Fin N) 𝕜 E) (a : Set.Iio N → 𝕜)
    {M : ℕ} (hM : N ≤ M) :
    schauderPartialSum 𝕜 (finiteBasisSequence b) a M =
      ∑ i : Fin N, a ⟨i.val, i.isLt⟩ • b i := by
  classical
  have hMN : M = N + (M - N) := (Nat.add_sub_of_le hM).symm
  simp only [schauderPartialSum, finiteBasisSequence, Set.mem_Iio]
  rw [hMN, sum_range_add]
  have hzero : (∑ i ∈ range (M - N), if h : N + i < N then
      a ⟨N + i, h⟩ • b ⟨N + i, h⟩ else 0) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp
  rw [hzero, add_zero]
  exact (sum_fin_eq_sum_range (fun i : Fin N => a ⟨i.val, i.isLt⟩ • b i)).symm

theorem finiteBasis_isSchauder (b : Basis (Fin N) 𝕜 E) :
    IsSchauderBasis 𝕜 (finiteBasisSequence b) := by
  refine ⟨?_, ?_⟩
  · intro i j hij hj
    exact lt_of_le_of_lt hij hj
  · intro x
    let a : Set.Iio N → 𝕜 := fun i => b.repr x ⟨i.val, i.property⟩
    have ha : Tendsto (schauderPartialSum 𝕜 (finiteBasisSequence b) a) atTop (𝓝 x) := by
      have heq : ∀ M, N ≤ M → schauderPartialSum 𝕜 (finiteBasisSequence b) a M = x := by
        intro M hM
        rw [schauderPartialSum_finiteBasis b a hM]
        exact b.sum_repr x
      exact tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun M hM => (heq M hM).symm)
    refine ⟨a, ha, ?_⟩
    intro c hc
    have hfull : (∑ i : Fin N, c ⟨i.val, i.isLt⟩ • b i) = x := by
      have ht : Tendsto (schauderPartialSum 𝕜 (finiteBasisSequence b) c) atTop
          (𝓝 (∑ i : Fin N, c ⟨i.val, i.isLt⟩ • b i)) :=
        tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun M hM =>
          (schauderPartialSum_finiteBasis b c hM).symm)
      exact tendsto_nhds_unique ht hc
    funext i
    have heq := congrArg (fun y => b.repr y ⟨i.val, i.property⟩) hfull
    simpa [a, Finsupp.single_apply] using heq

theorem finiteDimensional_hasSchauderBasis [FiniteDimensional 𝕜 E] :
    HasSchauderBasis 𝕜 E :=
  ⟨Set.Iio (Module.finrank 𝕜 E), finiteBasisSequence (Module.finBasis 𝕜 E),
    finiteBasis_isSchauder (Module.finBasis 𝕜 E)⟩

end SurveyStatements.P4
