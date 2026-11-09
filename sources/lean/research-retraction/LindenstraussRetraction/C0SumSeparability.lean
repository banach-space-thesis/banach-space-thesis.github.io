import LindenstraussRetraction.C0SumCoordinates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Bases

/-! Separability of the dependent c₀-sum, proved by its finite-coordinate images. -/

noncomputable section
open Filter Topology Set

namespace LindenstraussRetraction

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]

def c0SumFiniteInsertion (N : ℕ) (a : ∀ n : Fin N, E n.val) : C0Sum 𝕜 E :=
  ∑ n : Fin N, c0SumSingle 𝕜 E n.val (a n)

theorem c0SumFiniteInsertion_continuous (N : ℕ) :
    Continuous (c0SumFiniteInsertion 𝕜 E N) :=
  continuous_finset_sum _ (fun n _ => (c0SumSingle 𝕜 E n.val).continuous.comp
    (continuous_apply n))

theorem c0SumFiniteInsertion_coordinates (N : ℕ) (x : C0Sum 𝕜 E) :
    c0SumFiniteInsertion 𝕜 E N (fun n => x.val n.val) = c0SumTruncation 𝕜 E N x := by
  rw [c0SumFiniteInsertion]
  change (∑ n : Fin N, (fun m : ℕ => c0SumSingle 𝕜 E m (x.val m)) n.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => c0SumSingle 𝕜 E m (x.val m)) N]
  simp only [c0SumTruncation, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    c0SumCoordinate_apply]

theorem c0Sum_separable [∀ n, TopologicalSpace.SeparableSpace (E n)] :
    TopologicalSpace.SeparableSpace (C0Sum 𝕜 E) := by
  let s : Set (C0Sum 𝕜 E) := ⋃ N, Set.range (c0SumFiniteInsertion 𝕜 E N)
  have hs : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.isSeparable_iUnion.mpr
      (fun N => TopologicalSpace.isSeparable_range (c0SumFiniteInsertion_continuous 𝕜 E N))
  have hd : Dense s := by
    intro x
    apply mem_closure_of_tendsto (c0SumTruncation_tendsto 𝕜 E x)
    apply Filter.Eventually.of_forall
    intro N
    apply Set.mem_iUnion.mpr
    refine ⟨N, ?_⟩
    exact ⟨fun n => x.val n.val, c0SumFiniteInsertion_coordinates 𝕜 E N x⟩
  exact hd.isSeparable_iff.mp hs

end LindenstraussRetraction
