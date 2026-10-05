import ThesisCommon.Analysis.LpHaarConvergence
import ThesisCommon.Analysis.LpHaarAdjacentMeans

/-! Finite dyadic step reconstruction and density in genuine interval Lp. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical Function BigOperators Topology
namespace ThesisCommon

theorem lpHaarPartitionMean_eq_sum {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α]
    [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
    (hp : p ≠ ∞) (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hm : ∀ i, μ (s i) ≠ 0) (f : Lp 𝕜 p μ) :
    lpHaarPartitionMean hp s hs hd hc hm f =
      ∑ i, lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)
        (lpHaarMean hp (lebesgueLpRestrict (𝕜 := 𝕜) (s i) f)) := by
  apply (lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc).injective
  rw [map_sum]
  change lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc
    (lpHaarPartitionMean hp s hs hd hc hm f) =
      ∑ i, lebesgueLpPartition (𝕜 := 𝕜) hp s hs hd hc
        (lebesgueLpExtend (𝕜 := 𝕜) (s i) (hs i)
          (lpHaarMean hp (lebesgueLpRestrict (𝕜 := 𝕜) (s i) f)))
  simp_rw [lebesgueLpPartition_extend]
  apply lp.ext
  funext j
  rw [lpHaarPartitionMean_coordinate]
  simp [lp.coeFn_sum, lp.coeFn_single]
  rfl

theorem lpHaarIndicator_smul {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (c : 𝕜) :
    indicatorConstLp p hs (measure_ne_top μ s) c =
      c • indicatorConstLp p hs (measure_ne_top μ s) (1 : 𝕜) := by
  rw [← lpHaarExtend_const s hs c, ← lpHaarExtend_const s hs (1 : 𝕜), ← map_smul]
  congr 1
  change (Lp.constL p (μ.restrict s) 𝕜) c = c • (Lp.constL p (μ.restrict s) 𝕜) 1
  simpa using (map_smul (Lp.constL p (μ.restrict s) 𝕜) c (1 : 𝕜))

def lpHaarCellVector (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent) (n k : ℕ) : IntervalLp 𝕜 p :=
  indicatorConstLp p.val (show MeasurableSet (lpHaarCell n k) from measurableSet_Ioc)
    (measure_ne_top (volume.restrict (Icc (0 : ℝ) 1)) _) (1 : 𝕜)

theorem lpHaarDyadicMean_mem_stepSpan (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) (n : ℕ) (f : IntervalLp 𝕜 p) :
    lpHaarDyadicMean 𝕜 p hp n f ∈
      Submodule.span 𝕜 (Set.range (fun k : Fin (2 ^ n) => lpHaarCellVector 𝕜 p n k)) := by
  change lpHaarPartitionMean hp _ _ _ _ _ f ∈ _
  rw [lpHaarPartitionMean_eq_sum]
  apply Submodule.sum_mem
  intro k _
  rw [lpHaarMean_apply, lpHaarExtend_const, lpHaarIndicator_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem lpHaarCellVector_dense_span (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (hp : p.val ≠ ∞) :
    Dense (Submodule.span 𝕜 (Set.range (fun nk : Σ n : ℕ, Fin (2 ^ n) =>
      lpHaarCellVector 𝕜 p nk.1 nk.2)) : Set (IntervalLp 𝕜 p)) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lpHaarDyadicMean_tendsto 𝕜 p hp f)
  apply Eventually.of_forall
  intro n
  apply subset_closure
  apply Submodule.span_mono _ (lpHaarDyadicMean_mem_stepSpan 𝕜 p hp n f)
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨n, k⟩, rfl⟩

end ThesisCommon
