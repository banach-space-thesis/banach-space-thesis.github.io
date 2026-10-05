import ThesisCommon.Analysis.GowersMaureyBasisWeakNull
import ThesisCommon.Analysis.GowersMaureySpreadExhaustion
import ThesisCommon.Analysis.GowersMaureySchauderBasis

/-! The full tail-spread exhaustion is weakly null on every completed
vector, against every genuine bounded scalar functional. Finite basis
sums are handled by weak nullity of the basis; contractivity extends the
result using the actual Schauder expansions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem completedSpread_basisVector (D : ConstructionData 𝕜) (m n j : ℕ) :
    completedSpread D m n (basisVector D j) =
      if m ≤ j then basisVector D (j-m+n) else 0 := by
  rw [basisVector, completedSpread_denseEmbedding]
  change denseEmbedding D (spread m n (Finsupp.single j (1 : 𝕜))) = _
  rw [spread_single]
  split_ifs
  · rfl
  · exact map_zero _

theorem tendsto_functional_completedSpread_basisVector_zero (D : ConstructionData 𝕜)
    (φ : ShiftSpace D →L[𝕜] 𝕜) (j : ℕ) :
    Tendsto (fun z : ℕ×ℕ => φ (completedSpread D z.1 z.2 (basisVector D j)))
      cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (tendsto_functional_basisVector_zero D φ) ε hε
  filter_upwards [(spreadParameterSquare (max j N)).eventually_cofinite_notMem] with z hz
  rcases z with ⟨m,n⟩
  simp only [completedSpread_basisVector]
  split_ifs with hm
  · have hout := mt (mem_spreadParameterSquare m n (max j N)).mpr hz
    have hn : N ≤ j-m+n := by omega
    exact hN _ hn
  · simpa only [map_zero, dist_self] using hε

theorem tendsto_functional_completedSpread_finite_sum_zero (D : ConstructionData 𝕜)
    (φ : ShiftSpace D →L[𝕜] 𝕜) {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (c : ι → 𝕜) :
    Tendsto (fun z : ℕ×ℕ => φ (completedSpread D z.1 z.2
      (∑ i ∈ s, c i • basisVector D (a i)))) cofinite (𝓝 0) := by
  have h := tendsto_finset_sum s (fun i _ =>
    (tendsto_functional_completedSpread_basisVector_zero D φ (a i)).const_mul (c i))
  simpa only [map_sum, map_smul, smul_eq_mul, mul_zero, Finset.sum_const_zero] using h

theorem tendsto_functional_completedSpread_zero (D : ConstructionData 𝕜)
    (φ : ShiftSpace D →L[𝕜] 𝕜) (x : ShiftSpace D) :
    Tendsto (fun z : ℕ×ℕ => φ (completedSpread D z.1 z.2 x)) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2 * (‖φ‖+1))
  have hφ1 : 0 < ‖φ‖+1 := by positivity
  have hδ : 0 < δ := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (initialSum_tendsto D x) δ hδ
  let y := initialSum D N x
  have hxy : ‖x-y‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN N le_rfl
  have hy : Tendsto (fun z : ℕ×ℕ => φ (completedSpread D z.1 z.2 y)) cofinite (𝓝 0) := by
    simpa only [y, initialSum_apply] using
      tendsto_functional_completedSpread_finite_sum_zero D φ (Finset.range N) id
        (fun i => completedCoordinate D i x)
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε/2) (half_pos hε)] with z hz
  have hsmall : ‖φ (completedSpread D z.1 z.2 (x-y))‖ < ε/2 := by
    calc
      _ ≤ ‖φ‖ * ‖completedSpread D z.1 z.2 (x-y)‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * ‖x-y‖ := mul_le_mul_of_nonneg_left
        (completedSpread_norm_le D z.1 z.2 (x-y)) (norm_nonneg _)
      _ ≤ (‖φ‖+1) * ‖x-y‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖φ‖+1) * δ := mul_lt_mul_of_pos_left hxy hφ1
      _ = ε/2 := by dsimp only [δ]; field_simp
  have he : φ (completedSpread D z.1 z.2 x) =
      φ (completedSpread D z.1 z.2 (x-y)) + φ (completedSpread D z.1 z.2 y) := by
    rw [map_sub, map_sub]
    abel
  rw [dist_zero_right, he]
  have hz' : ‖φ (completedSpread D z.1 z.2 y)‖ < ε/2 := by
    simpa only [dist_zero_right] using hz
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem eventually_uniform_tailSpreadSquare_small (D : ConstructionData 𝕜)
    (φ : ShiftSpace D →L[𝕜] 𝕜) (x : ShiftSpace D) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ m n : ℕ,
      (m,n) ∉ spreadParameterSquare r → ‖φ (completedSpread D m n x)‖ < ε := by
  classical
  have hsmall := (Metric.tendsto_nhds.mp (tendsto_functional_completedSpread_zero D φ x)) ε hε
  simp only [dist_zero_right] at hsmall
  let B := {z : ℕ×ℕ | ¬ ‖φ (completedSpread D z.1 z.2 x)‖ < ε}
  have hB : B.Finite := eventually_cofinite.mp hsmall
  let F := hB.toFinset
  refine ⟨F.sup (fun z => max z.1 z.2), ?_⟩
  intro r hr m n hout
  by_contra h
  have hz : (m,n) ∈ F := hB.mem_toFinset.mpr h
  have hle := Finset.le_sup (f := fun z : ℕ×ℕ => max z.1 z.2) hz
  exact hout ((mem_spreadParameterSquare m n r).mpr
    ⟨(le_max_left _ _).trans (hle.trans hr), (le_max_right _ _).trans (hle.trans hr)⟩)

end ThesisCommon.GowersMaurey
