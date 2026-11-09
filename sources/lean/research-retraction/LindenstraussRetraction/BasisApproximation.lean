import LindenstraussRetraction.SchauderBasisLemmas
import LindenstraussRetraction.BidualMap
import LindenstraussRetraction.SoftRadial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite partial sums extend to the continuous bidual with the same norm. -/

noncomputable section
open Filter Topology
open scoped NNReal

namespace LindenstraussRetraction

universe u v
variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 200000

local instance approximationBidualNormedGroup : NormedAddCommGroup (Bidual 𝕜 X) := inferInstance
local instance approximationBidualNormedSpace : NormedSpace 𝕜 (Bidual 𝕜 X) := inferInstance
local instance approximationOperatorNorm : Norm (Bidual 𝕜 X →L[𝕜] X) :=
  ContinuousLinearMap.hasOpNorm (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := Bidual 𝕜 X) (F := X) (σ₁₂ := RingHom.id 𝕜)

def bidualEvaluate (f : StrongDual 𝕜 X) : Bidual 𝕜 X →L[𝕜] 𝕜 := by
  let L : Bidual 𝕜 X →ₗ[𝕜] 𝕜 :=
    { toFun := fun z => z f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.mkContinuous ‖f‖ (fun z => by simpa only [mul_comm] using z.le_opNorm f)

def basisBidualPartialSum (b : SchauderBasis 𝕜 X) (N : ℕ) : Bidual 𝕜 X →L[𝕜] X :=
  ∑ n ∈ Finset.range N, (bidualEvaluate (b.coord n)).smulRight (b.vector n)

@[simp] theorem basisBidualPartialSum_apply (b : SchauderBasis 𝕜 X) (N : ℕ)
    (z : Bidual 𝕜 X) :
    basisBidualPartialSum b N z = ∑ n ∈ Finset.range N, z (b.coord n) • b.vector n := by
  simp only [basisBidualPartialSum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

@[simp] theorem basisBidualPartialSum_embedding (b : SchauderBasis 𝕜 X) (N : ℕ) (x : X) :
    basisBidualPartialSum b N (bidualEmbedding 𝕜 X x) = b.partialSum N x := by
  simp only [basisBidualPartialSum_apply, bidualEmbedding_apply, b.partialSum_apply]

theorem transpose_partialSum (b : SchauderBasis 𝕜 X) (N : ℕ) (f : StrongDual 𝕜 X) :
    transpose (b.partialSum N) f = ∑ n ∈ Finset.range N, f (b.vector n) • b.coord n := by
  ext x
  simp only [transpose_apply, b.partialSum_apply, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro n _
  simp only [smul_eq_mul, mul_comm]

theorem basisBidualPartialSum_dual (b : SchauderBasis 𝕜 X) (N : ℕ)
    (z : Bidual 𝕜 X) (f : StrongDual 𝕜 X) :
    f (basisBidualPartialSum b N z) = z (transpose (b.partialSum N) f) := by
  rw [basisBidualPartialSum_apply, transpose_partialSum]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro n _
  simp only [smul_eq_mul, mul_comm]

theorem basisBidualPartialSum_norm_apply_le (b : SchauderBasis 𝕜 X) (N : ℕ)
    (z : Bidual 𝕜 X) : ‖basisBidualPartialSum b N z‖ ≤ ‖b.partialSum N‖*‖z‖ := by
  apply NormedSpace.norm_le_dual_bound 𝕜 (basisBidualPartialSum b N z)
    (M := ‖b.partialSum N‖*‖z‖) (mul_nonneg (norm_nonneg (b.partialSum N)) (norm_nonneg z))
  intro f
  rw [basisBidualPartialSum_dual]
  calc
    ‖z (transpose (b.partialSum N) f)‖ ≤ ‖z‖*‖transpose (b.partialSum N) f‖ := z.le_opNorm _
    _ ≤ ‖z‖*(‖b.partialSum N‖*‖f‖) := mul_le_mul_of_nonneg_left
      (((transpose (b.partialSum N)).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (norm_transpose_le _) (norm_nonneg f))) (norm_nonneg z)
    _ = (‖b.partialSum N‖*‖z‖)*‖f‖ := by ring

theorem basisBidualPartialSum_norm (b : SchauderBasis 𝕜 X) (N : ℕ) :
    ‖basisBidualPartialSum b N‖ = ‖b.partialSum N‖ := by
  apply le_antisymm
  · exact (basisBidualPartialSum b N).opNorm_le_bound (norm_nonneg (b.partialSum N))
      (basisBidualPartialSum_norm_apply_le b N)
  · apply (b.partialSum N).opNorm_le_bound (norm_nonneg (basisBidualPartialSum b N))
    intro x
    rw [← basisBidualPartialSum_embedding b N x]
    simpa only [LinearIsometry.norm_map] using
      (basisBidualPartialSum b N).le_opNorm (bidualEmbedding 𝕜 X x)

/-- A common bound for a pointwise identity approximation cannot be below one. -/
theorem lipschitz_approximation_constant_ge_one [Nontrivial X]
    (f : ℕ → X → X) (K : ℝ≥0) (hf : ∀ n, LipschitzWith K (f n))
    (ht : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 x)) : 1 ≤ K := by
  obtain ⟨x,hx⟩ := exists_ne (0 : X)
  have hd : 0 < dist x 0 := dist_pos.mpr hx
  have hb : dist x 0 ≤ (K : ℝ)*dist x 0 :=
    le_of_tendsto ((ht x).dist (ht 0)) (Filter.Eventually.of_forall (fun n => (hf n).dist_le_mul x 0))
  exact_mod_cast (by nlinarith : (1 : ℝ) ≤ (K : ℝ))

def basisPrefixSpan (b : SchauderBasis 𝕜 X) (N : ℕ) : Submodule 𝕜 X :=
  Submodule.span 𝕜 (Set.range (fun n : Fin N => b.vector n.val))

instance basisPrefixSpan_finiteDimensional (b : SchauderBasis 𝕜 X) (N : ℕ) :
    FiniteDimensional 𝕜 (basisPrefixSpan b N) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

theorem basisBidualPartialSum_mem (b : SchauderBasis 𝕜 X) (N : ℕ) (z : Bidual 𝕜 X) :
    basisBidualPartialSum b N z ∈ basisPrefixSpan b N := by
  rw [basisBidualPartialSum_apply]
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨n, Finset.mem_range.mp hn⟩, rfl⟩

def basisLipschitzApproximation (b : SchauderBasis 𝕜 X) (N : ℕ) (z : Bidual 𝕜 X) : X :=
  basisBidualPartialSum b N (softRadial 𝕜 ((N+1 : ℕ) : ℝ) z)

theorem basisBidualPartialSum_contractive (b : SchauderBasis 𝕜 X) (hb : b.IsMonotone)
    (N : ℕ) (z : Bidual 𝕜 X) : ‖basisBidualPartialSum b N z‖ ≤ ‖z‖ :=
  (basisBidualPartialSum_norm_apply_le b N z).trans (by
    nlinarith [hb N, norm_nonneg z])

theorem basisLipschitzApproximation_lipschitz (b : SchauderBasis 𝕜 X) (hb : b.IsMonotone)
    (N : ℕ) : LipschitzWith 1 (basisLipschitzApproximation b N) := by
  apply LipschitzWith.of_dist_le_mul (f := basisLipschitzApproximation b N)
  intro x y
  simp only [NNReal.coe_one, one_mul, basisLipschitzApproximation, dist_eq_norm, ← map_sub]
  apply le_trans (basisBidualPartialSum_contractive b hb N _)
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    (softRadial_lipschitz 𝕜 (by positivity : 0 < ((N+1 : ℕ) : ℝ))).dist_le_mul x y

theorem basisLipschitzApproximation_tendsto (b : SchauderBasis 𝕜 X) (hb : b.IsMonotone)
    (x : X) : Tendsto (fun N => basisLipschitzApproximation b N (bidualEmbedding 𝕜 X x))
      atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsoft := ((softRadial_tendsto 𝕜 (bidualEmbedding 𝕜 X x)).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => bidualEmbedding 𝕜 X x)
      atTop (𝓝 (bidualEmbedding 𝕜 X x)))).norm
  have hbase := ((b.tendsto_partialSum x).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))).norm
  simp only [sub_self, norm_zero] at hsoft hbase
  apply squeeze_zero (fun N => norm_nonneg _) _ (by simpa only [add_zero] using hsoft.add hbase)
  intro N
  calc
    ‖basisLipschitzApproximation b N (bidualEmbedding 𝕜 X x)-x‖ ≤
        ‖basisLipschitzApproximation b N (bidualEmbedding 𝕜 X x)-b.partialSum N x‖ +
          ‖b.partialSum N x-x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖softRadial 𝕜 ((N+1 : ℕ) : ℝ) (bidualEmbedding 𝕜 X x)-bidualEmbedding 𝕜 X x‖ +
          ‖b.partialSum N x-x‖ := by
      apply add_le_add_right
      rw [basisLipschitzApproximation, ← basisBidualPartialSum_embedding b N x, ← map_sub]
      exact basisBidualPartialSum_contractive b hb N _

theorem basisLipschitzApproximation_relativelyCompact (b : SchauderBasis 𝕜 X)
    (hb : b.IsMonotone) (N : ℕ) :
    IsCompact (closure (Set.range (basisLipschitzApproximation b N))) := by
  let V := basisPrefixSpan b N
  let R : ℝ := ((N+1 : ℕ) : ℝ)
  have hK : IsCompact ((Subtype.val : V → X) '' Metric.closedBall (0 : V) R) :=
    (isCompact_closedBall (0 : V) R).image continuous_subtype_val
  apply hK.of_isClosed_subset isClosed_closure
  apply hK.isClosed.closure_subset_iff.mpr
  rintro y ⟨z, rfl⟩
  let v : V := ⟨basisLipschitzApproximation b N z,
    basisBidualPartialSum_mem b N (softRadial 𝕜 R z)⟩
  refine ⟨v, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (basisBidualPartialSum_contractive b hb N (softRadial 𝕜 R z)).trans
    (softRadial_norm_le 𝕜 (by dsimp [R]; positivity) z)

/-- The exact special case of the soft approximation proposition needed for
the final space: a monotone Schauder basis gives compact-range approximations
on the whole continuous bidual with common Lipschitz constant one. -/
theorem basis_has_one_lipschitz_compactRange_approximation
    (b : SchauderBasis 𝕜 X) (hb : b.IsMonotone) :
    ∃ Ψ : ℕ → Bidual 𝕜 X → X,
      (∀ N, LipschitzWith 1 (Ψ N)) ∧
      (∀ N, IsCompact (closure (Set.range (Ψ N)))) ∧
      ∀ x : X, Tendsto (fun N => Ψ N (bidualEmbedding 𝕜 X x)) atTop (𝓝 x) :=
  ⟨basisLipschitzApproximation b, basisLipschitzApproximation_lipschitz b hb,
    basisLipschitzApproximation_relativelyCompact b hb, basisLipschitzApproximation_tendsto b hb⟩

theorem schauderBasis_nontrivial (b : SchauderBasis 𝕜 X) : Nontrivial X := by
  apply nontrivial_of_ne (b.vector 0) (0 : X)
  intro h
  have hc := b.biorthogonal 0 0
  rw [h, map_zero, if_pos rfl] at hc
  exact zero_ne_one hc

/-- No pointwise approximation to the identity on a space with a Schauder
basis has a common Lipschitz constant smaller than one. -/
theorem basis_lipschitz_approximation_optimal (b : SchauderBasis 𝕜 X)
    (f : ℕ → X → X) (K : ℝ≥0) (hf : ∀ N, LipschitzWith K (f N))
    (ht : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 x)) : 1 ≤ K := by
  letI : Nontrivial X := schauderBasis_nontrivial b
  exact lipschitz_approximation_constant_ge_one f K hf ht

end LindenstraussRetraction
