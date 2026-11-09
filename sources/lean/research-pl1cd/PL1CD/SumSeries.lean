import PL1CD.FiniteEntropy
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open scoped BigOperators

namespace PL1CD.Entropy

theorem finiteAverage_tsum {ι κ : Type*} [Fintype ι] (f : ι → κ → ℝ)
    (hf : ∀ a, Summable (f a)) :
    finiteAverage (fun a => ∑' i, f a i) = ∑' i, finiteAverage (fun a => f a i) := by
  unfold finiteAverage
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun a _ => hf a)]

end PL1CD.Entropy
