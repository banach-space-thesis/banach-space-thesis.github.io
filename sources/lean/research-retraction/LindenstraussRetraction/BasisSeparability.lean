import LindenstraussRetraction.SchauderBasisLemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Bases

/-! A countable Schauder basis over separable scalars makes its space separable. -/

noncomputable section
open Filter Topology Set

namespace LindenstraussRetraction.SchauderBasis

universe u v
variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : SchauderBasis 𝕜 X)

def finiteExpansion (N : ℕ) (a : Fin N → 𝕜) : X :=
  ∑ n : Fin N, a n • b.vector n.val

theorem finiteExpansion_continuous (N : ℕ) : Continuous (b.finiteExpansion N) :=
  continuous_finset_sum _ (fun n _ => (continuous_apply n).smul continuous_const)

theorem finiteExpansion_coordinates (N : ℕ) (x : X) :
    b.finiteExpansion N (fun n => b.coord n.val x) = b.partialSum N x := by
  rw [finiteExpansion]
  change (∑ n : Fin N, (fun m : ℕ => b.coord m x • b.vector m) n.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => b.coord m x • b.vector m) N]
  exact (b.partialSum_apply N x).symm

include b in
theorem separableSpace [TopologicalSpace.SeparableSpace 𝕜] :
    TopologicalSpace.SeparableSpace X := by
  let s : Set X := ⋃ N, Set.range (b.finiteExpansion N)
  have hs : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.isSeparable_iUnion.mpr
      (fun N => TopologicalSpace.isSeparable_range (b.finiteExpansion_continuous N))
  have hd : Dense s := by
    intro x
    apply mem_closure_of_tendsto (b.tendsto_partialSum x)
    apply Filter.Eventually.of_forall
    intro N
    apply Set.mem_iUnion.mpr
    refine ⟨N, ?_⟩
    exact ⟨fun n => b.coord n.val x, b.finiteExpansion_coordinates N x⟩
  exact hd.isSeparable_iff.mp hs

end LindenstraussRetraction.SchauderBasis
