import ThesisCommon.Analysis.SchauderSumUniformRows
import ThesisCommon.Analysis.SchauderSumMatrix
import ThesisCommon.Analysis.SchauderSymmetry
import ThesisCommon.Analysis.InfinityRestriction
import ThesisCommon.Analysis.FiniteColumnInterference

/-! The three interference estimates on the genuine mixed sum X(ell_infinity).
Scalar entries are evaluations of actual vectors and continuous linear maps. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace SchauderSum
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

def infinityCoordinate (i j : ℕ) : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜] 𝕜 :=
  (lpCoordinate ∞ j).comp (coordinate i)

def infinityEntry (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
    SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j r s : ℕ) : 𝕜 :=
  T (single r (lp.single ∞ s (1 : 𝕜))) i j

theorem infinity_block_row_sum_le
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j r : ℕ) (F : Finset ℕ) :
    ∑ s ∈ F, ‖infinityEntry T i j r s‖ ≤ ‖block T i r‖ :=
  infinity_operator_row_sum_le (block T i r) j F

theorem infinity_finite_interfering_sources (hs : b.HasSymmetricNorm)
    (hnot : ¬ b.EquivalentEllOne)
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (i j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {p : ℕ × ℕ | ε ≤ ‖infinityEntry T i j p.1 p.2‖}.Finite := by
  classical
  let φ := (infinityCoordinate (b := b) (hb := hb) i j).comp T
  obtain ⟨N, hN⟩ := uniform_unit_ball_row_bound
    (b.weakly_null_of_not_equivalentEllOne hs hnot) φ hε
  have htail (r : ℕ) : ∃ K, ∀ s, K ≤ s → ‖infinityEntry T i j r s‖ < ε := by
    have hsum := infinity_functional_row_summable (φ.comp (singleL r))
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hsum.tendsto_atTop_zero ε hε
    refine ⟨K, ?_⟩
    intro s hs
    simpa only [dist_zero_right, norm_norm] using hK s hs
  choose K hK using htail
  let F := (Finset.range N).biUnion (fun r =>
    (Finset.range (K r)).image (fun s => (r, s)))
  apply F.finite_toSet.subset
  rintro ⟨r, s⟩ hp
  have hr : r < N := by
    by_contra hr
    have hh := hN r (by omega) (lp.single ∞ s (1 : 𝕜))
      (by rw [lp.norm_single (by simp : (0 : ℝ≥0∞) < ∞), norm_one])
    exact (not_le_of_gt hh) hp
  have hs : s < K r := by
    by_contra hs
    exact (not_le_of_gt (hK r s (by omega))) hp
  exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr,
    Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩⟩

theorem infinity_simultaneous_small_rows
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (r : ℕ)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (K : Finset ℕ) (M : ℕ → Set ℕ)
    {A : Set ℕ} (hA : A.Infinite) (hM : ∀ i ∈ K, (M i).Infinite) :
    {s ∈ A | ∀ i ∈ K, {m ∈ M i | ‖infinityEntry T i m r s‖ < ε i}.Infinite}.Infinite := by
  apply bounded_columns_simultaneous_small_rows
    (fun i s m => ‖infinityEntry T i m r s‖) (fun i => ‖block T i r‖) ε
    (fun i m F => infinity_block_row_sum_le T i m r F) hε K M hA hM

theorem norm_apply_tendsto_zero (x : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) :
    Tendsto (fun i => ‖x i‖) atTop (𝓝 0) := by
  have hh := (b.coord_tendsto_zero (normVector x)).norm
  simpa only [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_zero]
    using hh

theorem infinity_target_row_tendsto_zero
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (r s : ℕ) :
    Tendsto (fun i => ⨆ j : ℕ, ‖infinityEntry T i j r s‖) atTop (𝓝 0) :=
  norm_apply_tendsto_zero (T (single r (lp.single ∞ s (1 : 𝕜))))

theorem infinity_finite_interfering_target_rows
    (T : SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞) →L[𝕜]
      SchauderSum b hb (lp (fun _ : ℕ => 𝕜) ∞)) (r s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    {i | ∃ j, ε ≤ ‖infinityEntry T i j r s‖}.Finite := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (norm_apply_tendsto_zero (T (single r (lp.single ∞ s (1 : 𝕜))))) ε hε
  apply (Finset.finite_toSet (Finset.range N)).subset
  rintro i ⟨j, hij⟩
  apply Finset.mem_range.mpr
  by_contra hi
  have hh := hN i (by omega)
  rw [dist_zero_right, norm_norm] at hh
  exact (not_le_of_gt hh) (hij.trans (lp.norm_apply_le_norm ENNReal.top_ne_zero _ j))

end SchauderSum
end ThesisCommon
