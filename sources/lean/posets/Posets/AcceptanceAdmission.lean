import Posets.AcceptanceMonotonicity
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem matrixAction_prefix_tail (M : ScalarMatrix 𝕜) (hM : HasBoundedRows 𝕜 M)
    (f : ℕ →ᵇ 𝕜) (j k : ℕ) :
    matrixAction 𝕜 M f k = (∑ n ∈ Finset.range (j + 1), M k n * f n) +
      matrixAction 𝕜 (matrixTail 𝕜 M j) f k := by
  have h := (summable_matrix_row M hM f k).sum_add_tsum_subtype_compl
    (Finset.range (j + 1))
  rw [show (∑' x : {x // x ∉ Finset.range (j + 1)}, M k x * f x) =
      ∑' n, ({x | x ∉ Finset.range (j + 1)} : Set ℕ).indicator
        (fun n => M k n * f n) n from
          tsum_subtype {x | x ∉ Finset.range (j + 1)} (fun n => M k n * f n)] at h
  simpa [Set.indicator_apply, Finset.mem_range, Nat.lt_succ_iff,
    not_le, matrixAction, matrixTail, ite_mul] using h.symm

/-- Finite column truncations approximate the action uniformly. -/
theorem compactMatrix_action_tendsto_zero (M : ScalarMatrix 𝕜)
    (hM : IsCompactMatrix 𝕜 M) (l : Filter ℕ)
    (hcol : ∀ n, Tendsto (fun k => M k n) l (𝓝 0)) (f : ℕ →ᵇ 𝕜) :
    Tendsto (matrixAction 𝕜 M f) l (𝓝 0) := by
  let F : ℕ → ℕ → 𝕜 := fun j k => ∑ n ∈ Finset.range (j + 1), M k n * f n
  have hu : TendstoUniformly F (matrixAction 𝕜 M f) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have ht : Tendsto (fun j => matrixNorm 𝕜 (matrixTail 𝕜 M j) * ‖f‖)
        atTop (𝓝 0) := by simpa using hM.2.mul_const ‖f‖
    filter_upwards [(tendsto_order.mp ht).2 ε hε] with j hj
    intro k
    rw [dist_eq_norm, matrixAction_prefix_tail M hM.1 f j k]
    change ‖F j k + matrixAction 𝕜 (matrixTail 𝕜 M j) f k - F j k‖ < ε
    rw [add_sub_cancel_left]
    exact (matrixAction_bound _ (boundedRows_matrixTail M hM.1 j) f k).trans_lt hj
  have hp (j : ℕ) : Tendsto (F j) l (𝓝 0) := by
    simpa [F] using tendsto_finset_sum (Finset.range (j + 1))
      (fun n _ => (hcol n).mul_const (f n))
  exact hu.tendsto_of_eventually_tendsto (Eventually.of_forall hp) tendsto_const_nhds

@[simp] theorem matrixAction_singleton (M : ScalarMatrix 𝕜) (n k : ℕ) :
    matrixAction 𝕜 M (indicator 𝕜 {n}) k = M k n := by
  unfold matrixAction
  rw [tsum_eq_single n (fun m hm => by simp [indicator, hm])]
  simp [indicator]

theorem eventually_mem_along (B : Set ℕ) : ∀ᶠ k in Along B, k ∈ B := by
  exact Filter.mem_inf_of_right (by simp)

theorem admits_of_accepts_not_undermines {𝒜 ℬ : Set (Set ℕ)} {M : ScalarMatrix 𝕜}
    (hacc : Accepts 𝕜 𝒜 ℬ M) (hu : ∀ B ∈ ℬ, ¬ Undermines 𝕜 B M) :
    Admits 𝕜 𝒜 ℬ M := by
  intro A hA B hB
  have hcol (n : ℕ) : Tendsto (fun k => M k n) (Along B) (𝓝 0) := by
    have hn : Tendsto (matrixAction 𝕜 M (indicator 𝕜 {n})) (Along B) (𝓝 0) :=
      not_not.mp (fun h => hu B hB ⟨n, h⟩)
    exact hn.congr (fun k => matrixAction_singleton M n k)
  have hr (n : ℕ) : Tendsto (fun k => matrixRestriction 𝕜 M A B k n)
      (Along B) (𝓝 0) := by
    by_cases hn : n ∈ A
    · apply (hcol n).congr'
      filter_upwards [eventually_mem_along B] with k hk
      simp [matrixRestriction, hk, hn]
    · simpa [matrixRestriction, hn] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : 𝕜)) (Along B) (𝓝 0))
  let f : ℕ →ᵇ 𝕜 := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (indicator 𝕜 A) 1 (fun n => by by_cases hn : n ∈ A <;> simp [indicator, hn])
  apply (compactMatrix_action_tendsto_zero _ (acceptsPair_of_accepts hacc hA hB)
    (Along B) hr f).congr'
  filter_upwards [eventually_mem_along B] with k hk
  apply tsum_congr
  intro n
  by_cases hn : n ∈ A <;> simp [f, matrixRestriction, indicator, hk, hn]

/-- Lemma 4.15: acceptance implies admission when columns vanish, and is
preserved on subsets of finite unions of the accepted families. -/
theorem lemma_4_15_proof (𝒜 ℬ : Set (Set ℕ)) (M : ScalarMatrix 𝕜) :
    Lemma_4_15 𝕜 𝒜 ℬ M := by
  intro _ _ hM hacc
  refine ⟨admits_of_accepts_not_undermines hacc, ?_⟩
  rintro C D _ _ ⟨F, hF, hC⟩ ⟨G, hG, hD⟩
  exact acceptsPair_of_finite_covers hM hacc F G hF hG C D hC hD

end Posets
