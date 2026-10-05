import ThesisCommon.Analysis.GowersMaureyCoordinates
import ThesisCommon.Analysis.SchauderBasis

/-! The actual coordinate vectors are an ordered normalized Schauder basis.
Convergence follows from contractive tail spreads and density of finite
sequences. No unconditionality or symmetric-norm assertion is made. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem finite_initial_sum (x : C00 𝕜) (N : ℕ) :
    x - spread N N x = ∑ i ∈ Finset.range N, x i • Finsupp.single i (1 : 𝕜) := by
  classical
  have h : (LinearMap.id - spread (𝕜 := 𝕜) N N) =
      ∑ i ∈ Finset.range N, (Finsupp.lsingle i).comp (Finsupp.lapply i) := by
    apply Finsupp.lhom_ext
    intro j c
    by_cases hj : j < N
    · have hn : ¬N ≤ j := by omega
      simp [spread_single, hn, Finsupp.single_apply, apply_ite, hj]
    · have hn : N ≤ j := by omega
      simp [spread_single, hn, Nat.sub_add_cancel hn, Finsupp.single_apply, apply_ite, hj]
  have hx := DFunLike.congr_fun h x
  simpa using hx

def initialSum (D : ConstructionData 𝕜) (N : ℕ) : ShiftSpace D →L[𝕜] ShiftSpace D :=
  ∑ i ∈ Finset.range N, (completedCoordinate D i).smulRight (basisVector D i)

theorem initialSum_apply (D : ConstructionData 𝕜) (N : ℕ) (x : ShiftSpace D) :
    initialSum D N x = ∑ i ∈ Finset.range N, completedCoordinate D i x • basisVector D i := by
  simp only [initialSum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

theorem initialSum_eq_id_sub_tail (D : ConstructionData 𝕜) (N : ℕ) :
    initialSum D N = ContinuousLinearMap.id 𝕜 (ShiftSpace D) - completedSpread D N N := by
  apply ContinuousLinearMap.ext
  intro x
  change initialSum D N x = x - completedSpread D N N x
  refine (denseEmbedding_denseRange D).induction_on x ?_ ?_
  · exact isClosed_eq (initialSum D N).continuous
      (continuous_id.sub (completedSpread D N N).continuous)
  · intro a
    rw [initialSum_apply, completedSpread_denseEmbedding, ← map_sub]
    simp only [completedCoordinate_denseEmbedding, basisVector, ← map_smul, ← map_sum]
    apply congrArg (denseEmbedding D)
    change (∑ i ∈ Finset.range N, (PreSpace.coefficients a) i • Finsupp.single i (1 : 𝕜)) =
      PreSpace.coefficients a - spread N N (PreSpace.coefficients a)
    exact (finite_initial_sum _ N).symm

theorem spread_eq_zero_of_support_lt (x : C00 𝕜) (N : ℕ)
    (hN : ∀ i ∈ x.support, i < N) : spread N N x = 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single x]
  simp only [map_finsuppSum]
  apply Finset.sum_eq_zero
  intro i hi
  dsimp only
  rw [spread_single, if_neg (by have := hN i hi; omega)]

theorem completedSpread_tail_tendsto_zero (D : ConstructionData 𝕜) (x : ShiftSpace D) :
    Tendsto (fun N : ℕ => completedSpread D N N x) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a, ha⟩ := (denseEmbedding_denseRange D).exists_dist_lt x hε
  rw [dist_eq_norm] at ha
  refine ⟨(PreSpace.coefficients a).support.sup id + 1, ?_⟩
  intro N hN
  have hsupport : ∀ i ∈ (PreSpace.coefficients a).support, i < N := by
    intro i hi
    have hi' : i ≤ (PreSpace.coefficients a).support.sup id := Finset.le_sup (f := id) hi
    omega
  have hz : completedSpread D N N (denseEmbedding D a) = 0 := by
    rw [completedSpread_denseEmbedding]
    have h := spread_eq_zero_of_support_lt (PreSpace.coefficients a) N hsupport
    have hp : PreSpace.spreadOperator (D := D) N N a = 0 := h
    rw [hp, map_zero]
  have hbound := completedSpread_norm_le D N N (x - denseEmbedding D a)
  rw [map_sub, hz, sub_zero] at hbound
  simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hbound.trans_lt ha

theorem initialSum_tendsto (D : ConstructionData 𝕜) (x : ShiftSpace D) :
    Tendsto (fun N => initialSum D N x) atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x) (f := (atTop : Filter ℕ))).sub
    (completedSpread_tail_tendsto_zero D x)
  simpa only [initialSum_eq_id_sub_tail, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, sub_zero] using h

def schauderBasis (D : ConstructionData 𝕜) : NormalizedSchauderBasis 𝕜 (ShiftSpace D) where
  vector := basisVector D
  coord := completedCoordinate D
  biorthogonal := completedCoordinate_basisVector D
  norm_vector := norm_basisVector D
  expansion x := by simpa only [initialSum_apply] using initialSum_tendsto D x

end ThesisCommon.GowersMaurey
