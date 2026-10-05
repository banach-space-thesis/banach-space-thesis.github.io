import Posets.BlockStatements
import PosetsCommon.CZeroSumTruncation

noncomputable section
set_option maxHeartbeats 1500000
open Filter Topology ThesisCommon
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem hasSeparableRange_sum {E F I : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (s : Finset I) (T : I → E →L[𝕜] F)
    (hT : ∀ i ∈ s, HasSeparableRange 𝕜 E F (T i)) :
    HasSeparableRange 𝕜 E F (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using JFA.hasSeparableRange_zero (𝕜 := 𝕜) (E := E) (F := F)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hT i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))

variable (X Z : ℕ → Type)
    [∀ n, NormedAddCommGroup (X n)] [∀ n, NormedSpace 𝕜 (X n)]
    [∀ n, NormedAddCommGroup (Z n)] [∀ n, NormedSpace 𝕜 (Z n)]

/-- The finite square of operator blocks used in the paper's proof. -/
def blockTruncation (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) (N : ℕ) :
    DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
    (sumInjection 𝕜 Z n).comp ((operatorBlock 𝕜 X Z T n m).comp (sumProjection 𝕜 X m))

theorem blockTruncation_eq (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) (N : ℕ) :
    blockTruncation X Z T N = (finiteProjection 𝕜 Z (Finset.range N)).comp
      (T.comp (finiteProjection 𝕜 X (Finset.range N))) := by
  ext x
  simp [blockTruncation, finiteProjection, operatorBlock, map_sum]

theorem blockTruncation_tendsto (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z)
    (x : DependentCZeroSum 𝕜 X) :
    Tendsto (fun N => blockTruncation X Z T N x) atTop (𝓝 (T x)) := by
  have hin := T.continuous.continuousAt.tendsto.comp (rangeProjection_tendsto 𝕜 X x)
  have hout := rangeProjection_tendsto 𝕜 Z (T x)
  have hbound : ∀ N,
      ‖blockTruncation X Z T N x - T x‖ ≤
      ‖T (finiteProjection 𝕜 X (Finset.range N) x) - T x‖ +
      ‖finiteProjection 𝕜 Z (Finset.range N) (T x) - T x‖ := by
    intro N
    rw [blockTruncation_eq]
    change ‖finiteProjection 𝕜 Z (Finset.range N)
      (T (finiteProjection 𝕜 X (Finset.range N) x)) - T x‖ ≤ _
    calc
      _ ≤ ‖finiteProjection 𝕜 Z (Finset.range N)
          (T (finiteProjection 𝕜 X (Finset.range N) x)) -
          finiteProjection 𝕜 Z (Finset.range N) (T x)‖ +
          ‖finiteProjection 𝕜 Z (Finset.range N) (T x) - T x‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          (finiteProjection 𝕜 Z (Finset.range N) (T (finiteProjection 𝕜 X (Finset.range N) x)))
          (finiteProjection 𝕜 Z (Finset.range N) (T x)) (T x)
      _ ≤ _ := by
        rw [← map_sub]
        exact add_le_add_right (finiteProjection_norm_le 𝕜 Z _ _) _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) hbound
  simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hin).add
    (tendsto_iff_norm_sub_tendsto_zero.mp hout)

/-- Corollary 6.19, using the printed finite-block approximations and Lemma 6.18. -/
theorem corollary_6_19_proof [∀ n, CompleteSpace (X n)] [∀ n, CompleteSpace (Z n)]
    (T : DependentCZeroSum 𝕜 X →L[𝕜] DependentCZeroSum 𝕜 Z) : Corollary_6_19 𝕜 X Z T := by
  constructor
  · intro hT n m
    exact (hT.comp_right (sumInjection 𝕜 X m)).comp_left (sumProjection 𝕜 Z n)
  · intro hblock
    apply lemma_6_18_proof (blockTruncation X Z T) T
    · intro N
      apply hasSeparableRange_sum
      intro n hn
      apply hasSeparableRange_sum
      intro m hm
      exact ((hblock n m).comp_right (sumProjection 𝕜 X m)).comp_left (sumInjection 𝕜 Z n)
    · exact blockTruncation_tendsto X Z T

end Posets
