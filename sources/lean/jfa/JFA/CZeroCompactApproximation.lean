import JFA.CZeroDiscreteTensor
import JFA.CompactIdeal

/-! Compact subsets of discrete C₀ have uniformly small coordinate tails.
Finite coordinate projections consequently approximate every compact operator
into this space in the actual operator norm. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
open scoped ZeroAtInfty
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
local instance : DecidableEq A := Classical.decEq A

def czeroTruncation (t : Finset A) : C₀(A, 𝕜) →L[𝕜] C₀(A, 𝕜) :=
  ∑ a ∈ t, (czeroEvaluation (𝕜 := 𝕜) a).smulRight (czeroDelta a)

@[simp] theorem czeroTruncation_apply (t : Finset A) (f : C₀(A, 𝕜)) (b : A) :
    czeroTruncation t f b = if b ∈ t then f b else 0 := by
  classical
  simp [czeroTruncation, ContinuousLinearMap.sum_apply, czero_sum_apply,
    czeroDelta_apply, czeroEvaluation]

theorem czero_compact_uniform_tail {K : Set C₀(A, 𝕜)} (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset A, ∀ f ∈ K, ∀ a ∉ t, ‖f a‖ < ε := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun f : C₀(A, 𝕜) => Metric.ball f (ε / 2)) (fun _ => Metric.isOpen_ball)
    (by intro f hf; exact mem_iUnion.mpr ⟨f, Metric.mem_ball_self (half_pos hε)⟩)
  choose K₀ hc₀ ht₀ using
    (fun f : C₀(A, 𝕜) => czero_vector_compact_tail f (ε / 2) (half_pos hε))
  let t : Finset A := s.biUnion (fun f => (hc₀ f).finite_of_discrete.toFinset)
  refine ⟨t, ?_⟩
  intro f hf a ha
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hs hf)
  have ha₀ : a ∉ K₀ g := by
    intro hag
    exact ha (Finset.mem_biUnion.mpr ⟨g, hg, (hc₀ g).finite_of_discrete.mem_toFinset.mpr hag⟩)
  have hfg' : ‖f a - g a‖ < ε / 2 :=
    lt_of_le_of_lt (by
      change ‖(f - g).toBCF a‖ ≤ ‖f - g‖
      exact (f - g).toBCF.norm_coe_le_norm a)
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hfg)
  have hga := ht₀ g a ha₀
  calc
    ‖f a‖ = ‖(f a - g a) + g a‖ := by rw [sub_add_cancel]
    _ ≤ ‖f a - g a‖ + ‖g a‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfg' hga
    _ = ε := add_halves ε

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_czeroTruncation_compact_approx (T : E →L[𝕜] C₀(A, 𝕜))
    (hT : IsCompactOperator T) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset A, ‖T - (czeroTruncation t).comp T‖ < ε := by
  have hlin : IsCompactOperator T.toLinearMap := hT
  obtain ⟨K, hK, hTK⟩ := hlin.image_closedBall_subset_compact 1
  obtain ⟨t, ht⟩ := czero_compact_uniform_tail hK (ε / 2) (half_pos hε)
  refine ⟨t, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
  intro x hx
  have hTx : T x ∈ K := hTK ⟨x, by simp only [Metric.mem_closedBall, dist_zero_right, hx, le_refl], rfl⟩
  change ‖(T x - czeroTruncation t (T x)).toBCF‖ ≤ ε / 2
  apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
  intro a
  change ‖T x a - czeroTruncation t (T x) a‖ ≤ ε / 2
  rw [czeroTruncation_apply]
  by_cases ha : a ∈ t
  · simp only [if_pos ha, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [if_neg ha, sub_zero]
    exact (ht (T x) hTx a ha).le

end JFA
