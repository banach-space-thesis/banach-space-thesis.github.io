import ThesisCommon.Analysis.LpHaarFiniteIntegral
import ThesisCommon.Analysis.LebesgueLpPartition

/-! Contractive averaging on a measurable partition of actual Lp. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Classical Function
namespace ThesisCommon

section Coordinate
variable {𝕜 ι : Type*} [RCLike 𝕜] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lpHaarCoordinateContractionValue (hp : 0 < p.toReal)
    (F : ∀ i, E i →L[𝕜] E i) (hF : ∀ i x, ‖F i x‖ ≤ ‖x‖) (x : lp E p) : lp E p :=
  ⟨fun i => F i (x i), memℓp_gen
    (((lp.memℓp x).summable hp).of_nonneg_of_le
      (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun i => Real.rpow_le_rpow (norm_nonneg _) (hF i (x i)) hp.le))⟩

theorem lpHaarCoordinateContractionValue_norm (hp : 0 < p.toReal)
    (F : ∀ i, E i →L[𝕜] E i) (hF : ∀ i x, ‖F i x‖ ≤ ‖x‖) (x : lp E p) :
    ‖lpHaarCoordinateContractionValue hp F hF x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le hp (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum hp]
  apply Summable.tsum_le_tsum
  · intro i
    exact Real.rpow_le_rpow (norm_nonneg _) (hF i (x i)) hp.le
  · exact (lp.memℓp (lpHaarCoordinateContractionValue hp F hF x)).summable hp
  · exact (lp.memℓp x).summable hp

def lpHaarCoordinateContraction (hp : 0 < p.toReal)
    (F : ∀ i, E i →L[𝕜] E i) (hF : ∀ i x, ‖F i x‖ ≤ ‖x‖) : lp E p →L[𝕜] lp E p :=
  LinearMap.mkContinuous
    { toFun := lpHaarCoordinateContractionValue hp F hF
      map_add' := fun x y => by
        apply lp.ext
        funext i
        exact map_add (F i) (x i) (y i)
      map_smul' := fun c x => by
        apply lp.ext
        funext i
        exact map_smul (F i) c (x i) }
    1 (fun x => by simpa only [one_mul] using lpHaarCoordinateContractionValue_norm hp F hF x)

theorem lpHaarCoordinateContraction_apply (hp : 0 < p.toReal)
    (F : ∀ i, E i →L[𝕜] E i) (hF : ∀ i x, ‖F i x‖ ≤ ‖x‖) (x : lp E p) (i : ι) :
    lpHaarCoordinateContraction hp F hF x i = F i (x i) := rfl

theorem lpHaarCoordinateContraction_norm (hp : 0 < p.toReal)
    (F : ∀ i, E i →L[𝕜] E i) (hF : ∀ i x, ‖F i x‖ ≤ ‖x‖) (x : lp E p) :
    ‖lpHaarCoordinateContraction hp F hF x‖ ≤ ‖x‖ :=
  lpHaarCoordinateContractionValue_norm hp F hF x
end Coordinate

section Partition
variable {𝕜 α ι : Type*} [RCLike 𝕜] [MeasurableSpace α] [Countable ι]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure α} [IsFiniteMeasure μ]
  (hp : p ≠ ∞) (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
  (hd : Pairwise (Disjoint on s)) (hc : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
  (hm : ∀ i, μ (s i) ≠ 0)

def lpHaarPartitionMean : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  let A := lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc
  let D := lpHaarCoordinateContraction
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)
    (fun i => lpHaarMean (𝕜 := 𝕜) (μ := μ.restrict (s i)) hp)
    (fun i => lpHaarMean_norm_le hp (by simpa using hm i))
  A.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (D.comp A.toContinuousLinearEquiv.toContinuousLinearMap)

theorem lpHaarPartitionMean_coordinate (f : Lp 𝕜 p μ) (i : ι) :
    lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc
      (lpHaarPartitionMean hp s hs hd hc hm f) i =
      lpHaarMean (𝕜 := 𝕜) (μ := μ.restrict (s i)) hp
        (lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc f i) := by
  simp only [lpHaarPartitionMean, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem lpHaarPartitionMean_norm (f : Lp 𝕜 p μ) :
    ‖lpHaarPartitionMean hp s hs hd hc hm f‖ ≤ ‖f‖ := by
  let A := lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc
  change ‖A.symm (lpHaarCoordinateContraction
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)
    (fun i => lpHaarMean (𝕜 := 𝕜) (μ := μ.restrict (s i)) hp)
    (fun i => lpHaarMean_norm_le hp (by simpa using hm i)) (A f))‖ ≤ ‖f‖
  rw [A.symm.norm_map]
  exact (lpHaarCoordinateContraction_norm _ _ _ (A f)).trans_eq (A.norm_map f)

theorem norm_lpHaarPartitionMean_le :
    ‖lpHaarPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using lpHaarPartitionMean_norm hp s hs hd hc hm f

theorem lpHaarPartitionMean_idempotent :
    (lpHaarPartitionMean (𝕜 := 𝕜) hp s hs hd hc hm).comp
      (lpHaarPartitionMean hp s hs hd hc hm) = lpHaarPartitionMean hp s hs hd hc hm := by
  apply ContinuousLinearMap.ext
  intro f
  apply (lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc).injective
  apply lp.ext
  funext i
  change lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc
    (lpHaarPartitionMean hp s hs hd hc hm (lpHaarPartitionMean hp s hs hd hc hm f)) i = _
  simp only [lpHaarPartitionMean_coordinate]
  exact congrArg (fun T : Lp 𝕜 p (μ.restrict (s i)) →L[𝕜] Lp 𝕜 p (μ.restrict (s i)) =>
    T (lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) hp s hs hd hc f i))
    (lpHaarMean_idempotent (𝕜 := 𝕜) hp (by simpa using hm i))
end Partition
end ThesisCommon
