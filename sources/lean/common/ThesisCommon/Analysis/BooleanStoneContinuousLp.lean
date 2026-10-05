import ThesisCommon.Analysis.BooleanStoneContinuousMeasurable
import ThesisCommon.Analysis.RCLikeLInfinitySimpleDensity
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! Actual C(Stone)-to-L∞ isometry for a finite measure positive on every
nonempty Stone clopen. If measurable sets have Stone representatives modulo
null sets, this isometry is onto. The sigma algebra remains the one generated
by Stone clopens; no Borel-space or countability hypothesis is substituted. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal
namespace ThesisCommon
variable {B 𝕜 : Type*} [BooleanAlgebra B] [RCLike 𝕜]
variable (μ : Measure (BooleanStonePoint B)) [IsFiniteMeasure μ]

theorem norm_booleanStone_continuous_toLp
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (f : C(BooleanStonePoint B, 𝕜)) :
    ‖(memLp_booleanStone_continuous f μ ∞).toLp f‖ = ‖f‖ := by
  let g : Lp 𝕜 ∞ μ := (memLp_booleanStone_continuous f μ ∞).toLp f
  have hgf : g =ᵐ[μ] f := MemLp.coeFn_toLp _
  apply le_antisymm
  · apply rclike_lInfinity_norm_le_of_ae_bound _ (norm_nonneg f)
    filter_upwards [hgf] with p hp
    rw [hp]
    exact f.norm_coe_le_norm p
  · apply (ContinuousMap.norm_le f (norm_nonneg g)).mpr
    intro p
    by_contra hp
    have hlt : ‖g‖ < ‖f p‖ := lt_of_not_ge hp
    have hU : IsOpen {q : BooleanStonePoint B | ‖g‖ < ‖f q‖} :=
      isOpen_lt continuous_const f.continuous.norm
    obtain ⟨U, ⟨a, rfl⟩, hpa, ha⟩ :=
      isTopologicalBasis_range_booleanStoneSet.mem_nhds_iff.mp (hU.mem_nhds hlt)
    have hpos := hμ a ((booleanStoneSet_nonempty_iff a).mp ⟨p, hpa⟩)
    have hz : μ (booleanStoneSet a) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hgf, rclike_lInfinity_ae_norm_le_norm g] with q hq hqbound
      intro hqa
      rw [hq] at hqbound
      exact (not_lt_of_ge hqbound) (ha hqa)
    exact (ne_of_gt hpos) hz

def booleanStoneContinuousLInfinityIsometry
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a)) :
    C(BooleanStonePoint B, 𝕜) →ₗᵢ[𝕜] Lp 𝕜 ∞ μ where
  toFun f := (memLp_booleanStone_continuous f μ ∞).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_booleanStone_continuous_toLp μ hμ

theorem booleanStoneContinuousLInfinityIsometry_coe
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (f : C(BooleanStonePoint B, 𝕜)) :
    booleanStoneContinuousLInfinityIsometry (𝕜 := 𝕜) μ hμ f =ᵐ[μ] f :=
  (memLp_booleanStone_continuous f μ ∞).coeFn_toLp

theorem booleanStone_indicator_mem_continuousLInfinity_range
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (A : Set (BooleanStonePoint B)) (hA : MeasurableSet A) (c : 𝕜)
    (hrep : ∃ a : B, A =ᵐ[μ] booleanStoneSet a) :
    indicatorConstLp ∞ hA (measure_ne_top μ _) c ∈
      range (booleanStoneContinuousLInfinityIsometry (𝕜 := 𝕜) μ hμ) := by
  obtain ⟨a, ha⟩ := hrep
  let f : C(BooleanStonePoint B, 𝕜) :=
    ⟨(booleanStoneSet a).indicator (fun _ => c),
      continuous_indicator (by simp [(isClopen_booleanStoneSet a)])
        continuous_const.continuousOn⟩
  refine ⟨f, ?_⟩
  apply Lp.ext
  filter_upwards [booleanStoneContinuousLInfinityIsometry_coe μ hμ f,
    (indicatorConstLp_coeFn : indicatorConstLp ∞ hA (measure_ne_top μ _) c =ᵐ[μ]
      A.indicator (fun _ => c)), ha] with p hp hpA hpa
  rw [hp, hpA]
  change (booleanStoneSet a).indicator (fun _ => c) p = A.indicator (fun _ => c) p
  change (p ∈ A) = (p ∈ booleanStoneSet a) at hpa
  simp only [Set.indicator]
  congr 1
  exact hpa.symm

theorem booleanStoneContinuousLInfinityIsometry_surjective
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (hrep : ∀ A : Set (BooleanStonePoint B), MeasurableSet A →
      ∃ a : B, A =ᵐ[μ] booleanStoneSet a) :
    Function.Surjective (booleanStoneContinuousLInfinityIsometry (𝕜 := 𝕜) μ hμ) := by
  let I := booleanStoneContinuousLInfinityIsometry (𝕜 := 𝕜) μ hμ
  have hclosed : IsClosed (range I) := I.antilipschitz.isClosed_range I.isometry.uniformContinuous
  intro f
  apply hclosed.closure_eq.subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨s, A, hA, happ⟩ := exists_rclike_lInfinity_indicator_sum_approximation f hε
  refine ⟨∑ c ∈ s, indicatorConstLp ∞ (hA c) (measure_ne_top μ _) c, ?_, ?_⟩
  · change _ ∈ LinearMap.range I.toLinearMap
    apply Submodule.sum_mem
    intro c hc
    exact booleanStone_indicator_mem_continuousLInfinity_range μ hμ (A c) (hA c) c (hrep _ (hA c))
  · simpa only [dist_eq_norm] using happ

def booleanStoneContinuousLInfinityEquiv
    (hμ : ∀ a : B, a ≠ ⊥ → 0 < μ (booleanStoneSet a))
    (hrep : ∀ A : Set (BooleanStonePoint B), MeasurableSet A →
      ∃ a : B, A =ᵐ[μ] booleanStoneSet a) :
    C(BooleanStonePoint B, 𝕜) ≃ₗᵢ[𝕜] Lp 𝕜 ∞ μ :=
  LinearIsometryEquiv.ofSurjective (booleanStoneContinuousLInfinityIsometry μ hμ)
    (booleanStoneContinuousLInfinityIsometry_surjective μ hμ hrep)

end ThesisCommon
