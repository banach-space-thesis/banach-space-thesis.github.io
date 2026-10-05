import JLMS.CZeroSum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Synthesis from uniformly controlled finite sums

When a family of coordinate operators has finite-sum norm bounded by the
largest coordinate norm, its sum defines a contraction on the dependent c₀
sum. Disjoint clopen extensions satisfy exactly this bound.
-/

noncomputable section
namespace JLMS
open Filter Topology
universe u v w
variable {𝕜 : Type w} [RCLike 𝕜] {I : Type u} {E : I → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

theorem summable_cZeroSum_coordinates
    (T : ∀ i, E i →L[𝕜] F)
    (hT : ∀ (x : ∀ i, E i) (s : Finset I) (M : ℝ), 0 ≤ M →
      (∀ i ∈ s, ‖x i‖ ≤ M) → ‖∑ i ∈ s, T i (x i)‖ ≤ M)
    (x : CZeroSum 𝕜 E) : Summable (fun i => T i (x i)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  let s : Finset I := (x.finite_norm_ge (half_pos hε)).toFinset
  refine ⟨s, fun t ht => (hT x t (ε / 2) (half_pos hε).le ?_).trans_lt (half_lt_self hε)⟩
  intro i hi
  apply le_of_not_ge
  intro hge
  have his : i ∈ s := by simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hge
  exact Finset.disjoint_left.mp ht hi his

theorem norm_cZeroSum_coordinates_tsum_le
    (T : ∀ i, E i →L[𝕜] F)
    (hT : ∀ (x : ∀ i, E i) (s : Finset I) (M : ℝ), 0 ≤ M →
      (∀ i ∈ s, ‖x i‖ ≤ M) → ‖∑ i ∈ s, T i (x i)‖ ≤ M)
    (x : CZeroSum 𝕜 E) : ‖∑' i, T i (x i)‖ ≤ ‖x‖ := by
  apply le_of_tendsto (summable_cZeroSum_coordinates T hT x).hasSum.norm
  exact Filter.Eventually.of_forall (fun s => hT x s ‖x‖ (norm_nonneg x)
    (fun i _ => x.norm_apply_le_norm i))

/-- The bounded sum of a disjointly supported family of coordinate maps. -/
def cZeroSumSynthesis
    (T : ∀ i, E i →L[𝕜] F)
    (hT : ∀ (x : ∀ i, E i) (s : Finset I) (M : ℝ), 0 ≤ M →
      (∀ i ∈ s, ‖x i‖ ≤ M) → ‖∑ i ∈ s, T i (x i)‖ ≤ M) :
    CZeroSum 𝕜 E →L[𝕜] F :=
  ({ toFun x := ∑' i, T i (x i)
     map_add' x y := by
       simp only [CZeroSum.add_apply, map_add]
       exact (summable_cZeroSum_coordinates T hT x).tsum_add
         (summable_cZeroSum_coordinates T hT y)
     map_smul' c x := by
       simp only [CZeroSum.smul_apply, map_smul]
       exact Summable.tsum_const_smul c (summable_cZeroSum_coordinates T hT x) } :
        CZeroSum 𝕜 E →ₗ[𝕜] F).mkContinuous 1
    (fun x => by simpa only [one_mul] using norm_cZeroSum_coordinates_tsum_le T hT x)

@[simp] theorem cZeroSumSynthesis_apply
    (T : ∀ i, E i →L[𝕜] F)
    (hT : ∀ (x : ∀ i, E i) (s : Finset I) (M : ℝ), 0 ≤ M →
      (∀ i ∈ s, ‖x i‖ ≤ M) → ‖∑ i ∈ s, T i (x i)‖ ≤ M)
    (x : CZeroSum 𝕜 E) : cZeroSumSynthesis T hT x = ∑' i, T i (x i) := rfl

theorem hasSum_cZeroSumSynthesis
    (T : ∀ i, E i →L[𝕜] F)
    (hT : ∀ (x : ∀ i, E i) (s : Finset I) (M : ℝ), 0 ≤ M →
      (∀ i ∈ s, ‖x i‖ ≤ M) → ‖∑ i ∈ s, T i (x i)‖ ≤ M)
    (x : CZeroSum 𝕜 E) : HasSum (fun i => T i (x i)) (cZeroSumSynthesis T hT x) :=
  (summable_cZeroSum_coordinates T hT x).hasSum

end JLMS
