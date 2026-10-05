import JFA.ContinuousTensor
import Mathlib.Topology.PartitionOfUnity

/-! Finite partitions of unity approximate every vector-valued continuous map
by finite sums of elementary tensors. Completeness then makes the isometric
tensor representation onto. -/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8000
open TopologicalSpace Topology Set
namespace JFA
variable {𝕜 : Type*} [RCLike 𝕜]
variable {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem exists_tensorContinuous_approx (g : C(M, X)) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : InjectiveTensor 𝕜 C(M, 𝕜) X, ‖g - tensorContinuousFunction z‖ < ε := by
  classical
  let U : M → Set M := fun x => {m | dist (g m) (g x) < ε / 2}
  have hopen : ∀ x, IsOpen (U x) := fun x =>
    Metric.isOpen_ball.preimage g.continuous
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro m hm
    exact mem_iUnion.mpr ⟨m, by simpa only [U, mem_setOf_eq, dist_self] using half_pos hε⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  have hfinitecover : (univ : Set M) ⊆ ⋃ i : t, U i.val := by
    intro m hm
    obtain ⟨i, hi, hmU⟩ := mem_iUnion₂.mp (ht hm)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hmU⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite isClosed_univ
    (fun i : t => U i.val) (fun i => hopen i.val) (locallyFinite_of_finite _) hfinitecover
  let φ : t → C(M, 𝕜) := fun i =>
    ⟨fun m => RCLike.ofReal (ρ i m), RCLike.continuous_ofReal.comp (ρ i).continuous⟩
  let z : InjectiveTensor 𝕜 C(M, 𝕜) X := ∑ i : t, injectivePure 𝕜 C(M, 𝕜) X (φ i) (g i.val)
  have hsum (m : M) : ∑ i : t, ρ i m = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ m)
  have hsumcast (m : M) : ∑ i : t, (RCLike.ofReal (ρ i m) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_sum, hsum, RCLike.ofReal_one]
  have hz (m : M) : tensorContinuousFunction z m = ∑ i : t, (RCLike.ofReal (ρ i m) : 𝕜) • g i.val := by
    simp only [z, map_sum, ContinuousMap.sum_apply, tensorContinuousFunction_pure, φ,
      ContinuousMap.coe_mk]
  have hpoint (m : M) : ‖g m - tensorContinuousFunction z m‖ ≤ ε / 2 := by
    have heq : g m - tensorContinuousFunction z m =
        ∑ i : t, (RCLike.ofReal (ρ i m) : 𝕜) • (g m - g i.val) := by
      rw [hz]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsumcast, one_smul]
    rw [heq]
    calc
      ‖∑ i : t, (RCLike.ofReal (ρ i m) : 𝕜) • (g m - g i.val)‖ ≤
          ∑ i : t, ‖(RCLike.ofReal (ρ i m) : 𝕜) • (g m - g i.val)‖ := norm_sum_le _ _
      _ ≤ ∑ i : t, ρ i m * (ε / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (ρ.nonneg i m)]
        by_cases hzero : ρ i m = 0
        · simp only [hzero, zero_mul, le_refl]
        · have hmU : m ∈ U i.val := hρ i (subset_tsupport _ (by exact hzero))
          have hdist : ‖g m - g i.val‖ ≤ ε / 2 := by
            change dist (g m) (g i.val) < ε / 2 at hmU
            simpa only [dist_eq_norm] using hmU.le
          exact mul_le_mul_of_nonneg_left hdist (ρ.nonneg i m)
      _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  refine ⟨z, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  exact (ContinuousMap.norm_le _ (le_of_lt (half_pos hε))).mpr hpoint

theorem tensorContinuousFunction_dense :
    DenseRange (tensorContinuousFunction (𝕜 := 𝕜) (M := M) (X := X)) := by
  apply Metric.denseRange_iff.mpr
  intro g ε hε
  obtain ⟨z, hz⟩ := exists_tensorContinuous_approx (𝕜 := 𝕜) g ε hε
  exact ⟨z, by simpa only [dist_eq_norm] using hz⟩

theorem tensorContinuousIsometry_surjective :
    Function.Surjective (tensorContinuousIsometry (𝕜 := 𝕜) (M := M) (X := X)) := by
  intro g
  have hclosed := (tensorContinuousIsometry (𝕜 := 𝕜) (M := M) (X := X)).isometry.isClosedEmbedding.isClosed_range
  have hg := tensorContinuousFunction_dense (𝕜 := 𝕜) (M := M) (X := X) g
  change g ∈ closure (range (tensorContinuousIsometry (𝕜 := 𝕜) (M := M) (X := X))) at hg
  rw [hclosed.closure_eq] at hg
  exact hg

def tensorContinuousEquiv : InjectiveTensor 𝕜 C(M, 𝕜) X ≃ₗᵢ[𝕜] C(M, X) :=
  LinearIsometryEquiv.ofSurjective tensorContinuousIsometry tensorContinuousIsometry_surjective

end JFA
