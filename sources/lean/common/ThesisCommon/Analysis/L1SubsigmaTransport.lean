import ThesisCommon.Analysis.MeasureAlgebraL1
import ThesisCommon.Analysis.L1SubsigmaConditionalMass
import ThesisCommon.Analysis.L1SubsigmaCut

/-! Transport of actual sub-sigma measurable L1 functions through an
isomorphism of trimmed measure algebras. -/
noncomputable section
open MeasureTheory Set Filter
namespace ThesisCommon
variable {X Y : Type*} {m₀ : MeasurableSpace X} {n₀ : MeasurableSpace Y}
variable (μ : @Measure X m₀) (ν : @Measure Y n₀) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {m : MeasurableSpace X} {n : MeasurableSpace Y} (hm : m ≤ m₀) (hn : n ≤ n₀)

theorem lOneSubsigmaEmbedding_retraction (f : Lp ℝ 1 μ) :
    lOneSubsigmaEmbedding μ hm (lOneSubsigmaRetraction μ hm f) =
      lOneSubsigmaProjection μ hm f :=
  DFunLike.congr_fun (lOneSubsigmaEmbedding_lift μ hm (lOneSubsigmaProjection μ hm)
    (lOneSubsigmaProjection_mem μ hm)) f

theorem lOneSubsigmaRetraction_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) :
    0 ≤ lOneSubsigmaRetraction μ hm f := by
  apply (lOneSubsigmaEmbedding_le_iff μ hm _ _).mp
  rw [map_zero, lOneSubsigmaEmbedding_retraction]
  exact lOneSubsigmaProjection_nonneg μ hm hf

theorem lOneSubsigmaRetraction_cut (A : Set X) (hA : MeasurableSet[m] A) (f : Lp ℝ 1 μ) :
    lOneSubsigmaRetraction μ hm (@lpCut ℝ _ X m₀ μ 1 A (hm A hA) f) =
      lpCut A hA (lOneSubsigmaRetraction μ hm f) := by
  apply (lOneSubsigmaEmbedding μ hm).injective
  rw [lOneSubsigmaEmbedding_retraction, lOneSubsigmaEmbedding_cut μ hm A hA,
    lOneSubsigmaEmbedding_retraction, lOneSubsigmaProjection_cut μ hm A hA]

def lOneSubsigmaTransport (Φ : MeasureAlgebraIso (μ.trim hm) (ν.trim hn)) :
    Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν :=
  (lOneSubsigmaEmbedding ν hn).toContinuousLinearMap.comp
    (Φ.lOneEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp (lOneSubsigmaRetraction μ hm))

theorem lOneSubsigmaTransport_mem (Φ : MeasureAlgebraIso (μ.trim hm) (ν.trim hn))
    (f : Lp ℝ 1 μ) :
    lOneSubsigmaTransport μ ν hm hn Φ f ∈ lOneSubsigma ν n := by
  change lOneSubsigmaTransport μ ν hm hn Φ f ∈ (lOneSubsigma ν n : Set (Lp ℝ 1 ν))
  rw [← range_lOneSubsigmaEmbedding ν hn]
  exact ⟨Φ.lOneEquiv (lOneSubsigmaRetraction μ hm f), rfl⟩

theorem lOneSubsigmaTransport_norm (Φ : MeasureAlgebraIso (μ.trim hm) (ν.trim hn))
    (f : Lp ℝ 1 μ) (hf : f ∈ lOneSubsigma μ m) :
    ‖lOneSubsigmaTransport μ ν hm hn Φ f‖ = ‖f‖ := by
  change ‖lOneSubsigmaEmbedding ν hn (Φ.lOneEquiv (lOneSubsigmaRetraction μ hm f))‖ = _
  rw [LinearIsometry.norm_map, LinearIsometryEquiv.norm_map,
    ← (lOneSubsigmaEmbedding μ hm).norm_map, lOneSubsigmaEmbedding_retraction,
    lOneSubsigmaProjection_eq_self μ hm f hf]

theorem lOneSubsigmaTransport_nonneg (Φ : MeasureAlgebraIso (μ.trim hm) (ν.trim hn))
    {f : Lp ℝ 1 μ} (hf : 0 ≤ f) : 0 ≤ lOneSubsigmaTransport μ ν hm hn Φ f := by
  change 0 ≤ lOneSubsigmaEmbedding ν hn (Φ.lOneEquiv (lOneSubsigmaRetraction μ hm f))
  rw [← map_zero (lOneSubsigmaEmbedding ν hn), lOneSubsigmaEmbedding_le_iff]
  exact (Φ.lOneEquiv_nonneg_iff _).mpr (lOneSubsigmaRetraction_nonneg μ hm hf)

theorem lOneSubsigmaTransport_indicator (Φ : MeasureAlgebraIso (μ.trim hm) (ν.trim hn))
    (A : Set X) (hA : MeasurableSet[m] A) (B : Set Y) (hB : MeasurableSet[n] B)
    (hAB : Φ.toEquiv (MeasureAlgebra.mk (μ.trim hm) A hA) = MeasureAlgebra.mk (ν.trim hn) B hB) :
    lOneSubsigmaTransport μ ν hm hn Φ (lOneIndicator (mX := m₀) μ A (hm A hA)) =
      lOneIndicator (mX := n₀) ν B (hn B hB) := by
  change lOneSubsigmaEmbedding ν hn
    (Φ.lOneEquiv (lOneSubsigmaRetraction μ hm (lOneIndicator (mX := m₀) μ A (hm A hA)))) = _
  rw [← lOneSubsigmaEmbedding_indicator μ hm A hA]
  have hret := DFunLike.congr_fun (lOneSubsigmaRetraction_embedding μ hm)
    (lOneIndicator (μ.trim hm) A hA)
  change lOneSubsigmaRetraction μ hm
    (lOneSubsigmaEmbedding μ hm (lOneIndicator (μ.trim hm) A hA)) =
      lOneIndicator (μ.trim hm) A hA at hret
  rw [hret, Φ.lOneEquiv_indicator_of_mk_eq A hA B hB hAB,
    lOneSubsigmaEmbedding_indicator]

theorem lOneSubsigmaTransport_cut (Φ : MeasureAlgebraIso (μ.trim hm) (ν.trim hn))
    (A : Set X) (hA : MeasurableSet[m] A) (B : Set Y) (hB : MeasurableSet[n] B)
    (hAB : Φ.toEquiv (MeasureAlgebra.mk (μ.trim hm) A hA) = MeasureAlgebra.mk (ν.trim hn) B hB)
    (f : Lp ℝ 1 μ) :
    lOneSubsigmaTransport μ ν hm hn Φ (@lpCut ℝ _ X m₀ μ 1 A (hm A hA) f) =
      @lpCut ℝ _ Y n₀ ν 1 B (hn B hB) (lOneSubsigmaTransport μ ν hm hn Φ f) := by
  change lOneSubsigmaEmbedding ν hn
    (Φ.lOneEquiv (lOneSubsigmaRetraction μ hm (@lpCut ℝ _ X m₀ μ 1 A (hm A hA) f))) = _
  rw [lOneSubsigmaRetraction_cut μ hm A hA, Φ.lOneEquiv_cut A hA,
    lOneSubsigmaEmbedding_cut ν hn (Φ.imageSet A hA) (Φ.measurableSet_imageSet A hA)]
  have hsets : Φ.imageSet A hA =ᵐ[ν] B := by
    apply ae_of_ae_trim hn
    exact (MeasureAlgebra.mk_eq_mk _ _).mp ((Φ.mk_imageSet A hA).trans hAB)
  change @lpCut ℝ _ Y n₀ ν 1 (Φ.imageSet A hA) _ (lOneSubsigmaTransport μ ν hm hn Φ f) =
    @lpCut ℝ _ Y n₀ ν 1 B _ (lOneSubsigmaTransport μ ν hm hn Φ f)
  apply Lp.ext
  filter_upwards [hsets,
    @lpCut_coe ℝ _ Y n₀ ν 1 (Φ.imageSet A hA) (hn _ (Φ.measurableSet_imageSet A hA))
      (lOneSubsigmaTransport μ ν hm hn Φ f),
    @lpCut_coe ℝ _ Y n₀ ν 1 B (hn B hB) (lOneSubsigmaTransport μ ν hm hn Φ f)] with y hy h₁ h₂
  rw [h₁, h₂]
  change (y ∈ Φ.imageSet A hA) = (y ∈ B) at hy
  by_cases hyB : y ∈ B <;> simp [hy, hyB]

end ThesisCommon


