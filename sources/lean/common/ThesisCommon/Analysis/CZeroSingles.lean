import ThesisCommon.Analysis.DisjointSequenceBlocks
import ThesisCommon.Analysis.SequencePrefixes
import ThesisCommon.Analysis.SequenceCoordinates

/-! Single-coordinate vectors and their finite disjoint signed sums in c₀. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A vector supported on one natural coordinate is an actual null sequence. -/
def cZeroSingle (i : ℕ) (x : X) : CZeroSum X where
  toFun n := if n = i then x else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with n hn
    simp [ne_of_gt hn]

@[simp] theorem cZeroSingle_apply (i n : ℕ) (x : X) :
    cZeroSingle i x n = if n = i then x else 0 := rfl

theorem norm_cZeroSingle_le (i : ℕ) (x : X) : ‖cZeroSingle i x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro n
  change ‖if n = i then x else 0‖ ≤ ‖x‖
  split_ifs <;> simp

/-- Bounded coordinate insertion from X to c₀(X). -/
def cZeroSingleCLM (i : ℕ) : X →L[𝕜] CZeroSum X :=
  LinearMap.mkContinuous
    { toFun := cZeroSingle i
      map_add' := by intro x y; ext n; simp; split_ifs <;> simp
      map_smul' := by intro a x; ext n; simp }
    1 (fun x => by simpa using norm_cZeroSingle_le i x)

@[simp] theorem cZeroSingleCLM_apply (i : ℕ) (x : X) :
    cZeroSingleCLM (𝕜 := 𝕜) i x = cZeroSingle i x := rfl

/-- Disjoint finite single-coordinate embeddings have signed-sum norm at most one. -/
theorem cZero_single_embedding_sign_bound {n : ℕ} (e : Fin n ↪ ℕ)
    (x : Fin n → X) (hx : ∀ i, ‖x i‖ ≤ 1) (θ : Fin n → Bool) :
    ‖∑ i, if θ i then cZeroSingleCLM (𝕜 := 𝕜) (e i) (x i)
      else -(cZeroSingleCLM (𝕜 := 𝕜) (e i) (x i))‖ ≤ 1 := by
  apply cZero_norm_sign_sum_le _ _ _ θ
  · intro i
    exact (norm_cZeroSingle_le (e i) (x i)).trans (hx i)
  · intro i j hij k
    by_cases hk : k = e i
    · right
      have hkj : k ≠ e j := by intro hh; exact hij (e.injective (hk.symm.trans hh))
      simp [hkj]
    · left
      simp [hk]

/-- The c₀ prefix also has the exact finite single-coordinate expansion. -/
theorem cZeroPrefix_eq_sum_single (k : ℕ) (x : CZeroSum X) :
    cZeroPrefix k x = ∑ j ∈ Finset.range (k + 1), cZeroSingle j (x j) := by
  ext n
  change (if n ≤ k then x n else 0) = (∑ j ∈ Finset.range (k + 1), cZeroSingle j (x j)) n
  let ev : CZeroSum X →+ X :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change (if n ≤ k then x n else 0) = ev
    (∑ j ∈ Finset.range (k + 1), cZeroSingle j (x j))
  rw [map_sum]
  change (if n ≤ k then x n else 0) = ∑ j ∈ Finset.range (k + 1), if n = j then x j else 0
  by_cases hn : n ≤ k
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp [Finset.mem_range, Nat.lt_succ_iff, hn]
  · rw [if_neg hn]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have : n ≠ j := by intro heq; subst j; exact hn (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    simp [this]

end ThesisCommon
