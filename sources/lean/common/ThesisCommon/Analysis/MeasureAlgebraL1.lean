import ThesisCommon.Analysis.MeasureAlgebraIndicators
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.Analysis.Normed.Operator.Mul
import ThesisCommon.LpCut

/-! The genuine real L1 lattice isometry induced by an arbitrary isomorphism
of finite measure algebras. Indicators are extended through integrable simple
functions and their L1 limits; no underlying point map is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Classical

namespace ThesisCommon.MeasureAlgebraIso
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable (Φ : MeasureAlgebraIso μ ν)

def lOneIndicatorMap (s : Set X) : ℝ →L[ℝ] Lp ℝ 1 ν :=
  if hs : MeasurableSet s then
    ContinuousLinearMap.toSpanSingleton ℝ
      (lOneIndicator ν (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs))
  else 0

omit [IsFiniteMeasure μ] in
theorem lOneIndicatorMap_apply (s : Set X) (hs : MeasurableSet s) (c : ℝ) :
    Φ.lOneIndicatorMap s c =
      c • lOneIndicator ν (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs) := by
  simp only [lOneIndicatorMap, dif_pos hs, ContinuousLinearMap.toSpanSingleton_apply]

omit [IsFiniteMeasure μ] in
theorem lOneIndicatorMap_finMeasAdditive : FinMeasAdditive μ Φ.lOneIndicatorMap := by
  intro s t hs ht _ _ hst
  apply ContinuousLinearMap.ext
  intro c
  rw [Φ.lOneIndicatorMap_apply _ (hs.union ht), ContinuousLinearMap.add_apply,
    Φ.lOneIndicatorMap_apply _ hs, Φ.lOneIndicatorMap_apply _ ht, ← smul_add]
  congr 1
  calc
    lOneIndicator ν (Φ.imageSet (s ∪ t) (hs.union ht)) _ =
        lOneIndicator ν (Φ.imageSet s hs ∪ Φ.imageSet t ht)
          ((Φ.measurableSet_imageSet s hs).union (Φ.measurableSet_imageSet t ht)) :=
      lOneIndicator_eq_of_ae _ _ (Φ.imageSet_union_ae s t hs ht)
    _ = lOneIndicator ν (Φ.imageSet s hs) _ + lOneIndicator ν (Φ.imageSet t ht) _ :=
      lOneIndicator_union_of_inter_null _ _ _ _ (Φ.imageSet_inter_null_of_disjoint s t hs ht hst)

omit [IsFiniteMeasure μ] in
theorem lOneIndicatorMap_dominated : DominatedFinMeasAdditive μ Φ.lOneIndicatorMap 1 := by
  refine ⟨Φ.lOneIndicatorMap_finMeasAdditive, ?_⟩
  intro s hs _
  rw [lOneIndicatorMap, dif_pos hs, ContinuousLinearMap.norm_toSpanSingleton,
    norm_lOneIndicator, one_mul]
  exact le_of_eq (congrArg ENNReal.toReal (Φ.measure_imageSet s hs))

/-- Extension of the transported indicators to an actual bounded real linear map. -/
def lOneMap : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 ν := L1.setToL1 Φ.lOneIndicatorMap_dominated

theorem lOneMap_indicator (s : Set X) (hs : MeasurableSet s) :
    Φ.lOneMap (lOneIndicator μ s hs) =
      lOneIndicator ν (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs) := by
  have h := L1.setToL1_indicatorConstLp Φ.lOneIndicatorMap_dominated hs (measure_ne_top μ s) (1 : ℝ)
  rw [indicatorConstLp_eq_smul_lOneIndicator, one_smul, Φ.lOneIndicatorMap_apply, one_smul] at h
  exact h

omit [IsFiniteMeasure μ] in
theorem lOneMap_norm_le (f : Lp ℝ 1 μ) : ‖Φ.lOneMap f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using
    L1.norm_setToL1_le_mul_norm Φ.lOneIndicatorMap_dominated zero_le_one f

omit [IsFiniteMeasure μ] in
theorem lOneMap_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) : 0 ≤ Φ.lOneMap f := by
  apply L1.setToL1_nonneg Φ.lOneIndicatorMap_dominated _ hf
  intro s hs _ c hc
  rw [Φ.lOneIndicatorMap_apply _ hs]
  exact smul_nonneg hc (lOneIndicator_nonneg _ _)

omit [IsFiniteMeasure μ] in
theorem lOneMap_mono : Monotone Φ.lOneMap := by
  intro f g hfg
  apply sub_nonneg.mp
  rw [← map_sub]
  exact Φ.lOneMap_nonneg (sub_nonneg.mpr hfg)

theorem lOneMap_symm_comp : Φ.symm.lOneMap.comp Φ.lOneMap = ContinuousLinearMap.id ℝ (Lp ℝ 1 μ) := by
  apply lOne_continuousLinearMap_ext_indicators
  intro s hs
  rw [ContinuousLinearMap.comp_apply, Φ.lOneMap_indicator, Φ.symm.lOneMap_indicator,
    ContinuousLinearMap.id_apply]
  exact lOneIndicator_eq_of_ae _ hs (Φ.symm_imageSet_imageSet_ae s hs)

theorem lOneMap_symm_apply (f : Lp ℝ 1 μ) : Φ.symm.lOneMap (Φ.lOneMap f) = f :=
  DFunLike.congr_fun Φ.lOneMap_symm_comp f

theorem lOneMap_apply_symm (g : Lp ℝ 1 ν) : Φ.lOneMap (Φ.symm.lOneMap g) = g := by
  have h := Φ.symm.lOneMap_symm_apply g
  exact h

theorem lOneMap_norm (f : Lp ℝ 1 μ) : ‖Φ.lOneMap f‖ = ‖f‖ := by
  apply le_antisymm (Φ.lOneMap_norm_le f)
  simpa only [Φ.lOneMap_symm_apply] using Φ.symm.lOneMap_norm_le (Φ.lOneMap f)

theorem lOneMap_surjective : Function.Surjective Φ.lOneMap :=
  fun g => ⟨Φ.symm.lOneMap g, Φ.lOneMap_apply_symm g⟩

/-- Every measure-preserving isomorphism of finite measure algebras induces a
surjective real L1 linear isometry, constructed by extending its indicator map. -/
def lOneEquiv : Lp ℝ 1 μ ≃ₗᵢ[ℝ] Lp ℝ 1 ν :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := Φ.lOneMap.toLinearMap, norm_map' := Φ.lOneMap_norm }
    Φ.lOneMap_surjective

theorem lOneEquiv_apply (f : Lp ℝ 1 μ) : Φ.lOneEquiv f = Φ.lOneMap f := rfl

theorem lOneEquiv_symm_apply (g : Lp ℝ 1 ν) : Φ.lOneEquiv.symm g = Φ.symm.lOneMap g := by
  apply Φ.lOneEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply, lOneEquiv_apply, Φ.lOneMap_apply_symm]

theorem lOneEquiv_indicator (s : Set X) (hs : MeasurableSet s) :
    Φ.lOneEquiv (lOneIndicator μ s hs) =
      lOneIndicator ν (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs) :=
  Φ.lOneMap_indicator s hs

theorem lOneEquiv_indicator_of_mk_eq (s : Set X) (hs : MeasurableSet s)
    (t : Set Y) (ht : MeasurableSet t)
    (hst : Φ.toEquiv (MeasureAlgebra.mk μ s hs) = MeasureAlgebra.mk ν t ht) :
    Φ.lOneEquiv (lOneIndicator μ s hs) = lOneIndicator ν t ht := by
  rw [Φ.lOneEquiv_indicator]
  apply lOneIndicator_eq_of_ae _ ht
  apply (MeasureAlgebra.mk_eq_mk _ ht).mp
  exact (Φ.mk_imageSet s hs).trans hst

theorem lOneEquiv_le_iff (f g : Lp ℝ 1 μ) :
    Φ.lOneEquiv f ≤ Φ.lOneEquiv g ↔ f ≤ g := by
  change Φ.lOneMap f ≤ Φ.lOneMap g ↔ f ≤ g
  constructor
  · intro h
    simpa only [Φ.lOneMap_symm_apply] using Φ.symm.lOneMap_mono h
  · intro h
    exact Φ.lOneMap_mono h

def lOneOrderIso : Lp ℝ 1 μ ≃o Lp ℝ 1 ν where
  toEquiv := Φ.lOneEquiv.toEquiv
  map_rel_iff' := fun {f g} => Φ.lOneEquiv_le_iff f g

theorem lOneEquiv_sup (f g : Lp ℝ 1 μ) :
    Φ.lOneEquiv (f ⊔ g) = Φ.lOneEquiv f ⊔ Φ.lOneEquiv g :=
  Φ.lOneOrderIso.map_sup f g

theorem lOneEquiv_inf (f g : Lp ℝ 1 μ) :
    Φ.lOneEquiv (f ⊓ g) = Φ.lOneEquiv f ⊓ Φ.lOneEquiv g :=
  Φ.lOneOrderIso.map_inf f g

theorem lOneEquiv_abs (f : Lp ℝ 1 μ) : Φ.lOneEquiv |f| = |Φ.lOneEquiv f| := by
  change Φ.lOneEquiv (f ⊔ -f) = Φ.lOneEquiv f ⊔ -Φ.lOneEquiv f
  rw [Φ.lOneEquiv_sup, map_neg]

theorem lOneEquiv_nonneg_iff (f : Lp ℝ 1 μ) : 0 ≤ Φ.lOneEquiv f ↔ 0 ≤ f := by
  simpa only [map_zero] using Φ.lOneEquiv_le_iff 0 f

omit [MeasurableSpace Y] [IsFiniteMeasure ν] in
theorem lpCut_lOneIndicator (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    lpCut s hs (lOneIndicator μ t ht) = lOneIndicator μ (s ∩ t) (hs.inter ht) := by
  apply Lp.ext
  filter_upwards [lpCut_coe s hs (lOneIndicator μ t ht),
    lOneIndicator_coe (μ := μ) t ht,
    lOneIndicator_coe (μ := μ) (s ∩ t) (hs.inter ht)] with x hcut ht' hinter
  rw [hcut, hinter]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp_all

/-- Indicator multiplication is transported by the measure-algebra isomorphism. -/
theorem lOneEquiv_cut (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 1 μ) :
    Φ.lOneEquiv (lpCut s hs f) =
      lpCut (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs) (Φ.lOneEquiv f) := by
  have hmap : Φ.lOneMap.comp (lpCutL s hs) =
      (lpCutL (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs)).comp Φ.lOneMap := by
    apply lOne_continuousLinearMap_ext_indicators
    intro t ht
    change Φ.lOneMap (lpCut s hs (lOneIndicator μ t ht)) =
      lpCut (Φ.imageSet s hs) (Φ.measurableSet_imageSet s hs)
        (Φ.lOneMap (lOneIndicator μ t ht))
    rw [lpCut_lOneIndicator, Φ.lOneMap_indicator, Φ.lOneMap_indicator, lpCut_lOneIndicator]
    exact lOneIndicator_eq_of_ae _ _ (Φ.imageSet_inter_ae s t hs ht)
  exact DFunLike.congr_fun hmap f

end ThesisCommon.MeasureAlgebraIso
