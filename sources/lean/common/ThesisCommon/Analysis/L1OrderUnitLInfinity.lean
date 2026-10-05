import ThesisCommon.Analysis.LInfinityL1Pairing
import ThesisCommon.Analysis.FiniteL1UnitStone

/-! A genuine unital order isomorphism between finite real L1 spaces extends
to an isometric order isomorphism of their actual L-infinity spaces. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace ThesisCommon
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def linftyToL1 : Lp ℝ ∞ μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun f := ((Lp.memLp f).mono_exponent le_top).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f+g)).mono_exponent le_top),
      Lp.coeFn_add f g, Lp.coeFn_add
        (((Lp.memLp f).mono_exponent le_top).toLp f)
        (((Lp.memLp g).mono_exponent le_top).toLp g),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent le_top),
      MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent le_top)] with x h hfg hadd hf hg
    simp only [Pi.add_apply] at *
    exact h.trans (hfg.trans (hadd.trans (congrArg₂ (· + ·) hf hg)).symm)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent le_top),
      Lp.coeFn_smul c f, Lp.coeFn_smul c (((Lp.memLp f).mono_exponent le_top).toLp f),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent le_top)] with x h hcf hs hf
    simp only [Pi.smul_apply] at *
    exact h.trans (hcf.trans (hs.trans (congrArg (c • ·) hf)).symm)

theorem linftyToL1_coe (f : Lp ℝ ∞ μ) : linftyToL1 μ f =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (p := 1) le_top)

theorem linftyToL1_injective : Function.Injective (linftyToL1 μ) := by
  intro f g h
  apply Lp.ext
  exact (linftyToL1_coe μ f).symm.trans ((Lp.ext_iff.mp h).trans (linftyToL1_coe μ g))

theorem linftyToL1_nonneg (f : Lp ℝ ∞ μ) : 0 ≤ linftyToL1 μ f ↔ 0 ≤ f := by
  rw [← Lp.coeFn_nonneg, ← Lp.coeFn_nonneg]
  exact Filter.eventually_congr ((linftyToL1_coe μ f).mono fun x hx => by rw [hx])

theorem linftyToL1_one : linftyToL1 μ (linftyOne μ) = lOneUnit μ := by
  apply Lp.ext
  filter_upwards [linftyToL1_coe μ (linftyOne μ), linftyOne_coe (μ := μ),
    lOneIndicator_coe (μ := μ) univ MeasurableSet.univ] with x h ho hunit
  simp only [indicator_univ] at hunit
  exact h.trans (ho.trans hunit.symm)

theorem lOne_le_smul_unit_iff (f : Lp ℝ 1 μ) (c : ℝ) :
    f ≤ c • lOneUnit μ ↔ ∀ᵐ x ∂μ, f x ≤ c := by
  rw [← Lp.coeFn_le]
  apply Filter.eventually_congr
  filter_upwards [Lp.coeFn_smul c (lOneUnit μ),
    lOneIndicator_coe (μ := μ) univ MeasurableSet.univ] with x hs ho
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  simp only [indicator_univ, Pi.one_apply] at ho
  rw [hs, ho, mul_one]

theorem lOne_interval_unit_iff (f : Lp ℝ 1 μ) (c : ℝ) :
    (-c) • lOneUnit μ ≤ f ∧ f ≤ c • lOneUnit μ ↔ ∀ᵐ x ∂μ, ‖f x‖ ≤ c := by
  have hl : (-c) • lOneUnit μ ≤ f ↔ -f ≤ c • lOneUnit μ := by
    rw [neg_le, ← neg_smul]
  rw [hl, lOne_le_smul_unit_iff, lOne_le_smul_unit_iff, ← Filter.eventually_and]
  apply Filter.eventually_congr
  filter_upwards [Lp.coeFn_neg f] with x hx
  simp only [Pi.neg_apply] at hx
  rw [hx, Real.norm_eq_abs, abs_le]
  exact and_congr neg_le Iff.rfl

variable {μ ν}
variable (e : Lp ℝ 1 μ ≃ₗᵢ[ℝ] Lp ℝ 1 ν)
variable (he : ∀ f, 0 ≤ e f ↔ 0 ≤ f) (hone : e (lOneUnit μ) = lOneUnit ν)

include he in
theorem lOneOrderUnitEquiv_le_iff (f g : Lp ℝ 1 μ) : e f ≤ e g ↔ f ≤ g := by
  simpa only [map_sub, sub_nonneg] using he (g-f)

include he hone in
theorem lOneOrderUnitEquiv_bound (f : Lp ℝ ∞ μ) :
    ∀ᵐ y ∂ν, ‖e (linftyToL1 μ f) y‖ ≤ ‖f‖ := by
  apply (lOne_interval_unit_iff ν _ _).mp
  have hb : (-‖f‖) • lOneUnit μ ≤ linftyToL1 μ f ∧
      linftyToL1 μ f ≤ ‖f‖ • lOneUnit μ := by
    apply (lOne_interval_unit_iff μ _ _).mpr
    filter_upwards [linftyToL1_coe μ f, linfty_ae_norm_le_norm f] with x hx hb
    simpa only [hx] using hb
  constructor
  · simpa only [map_smul, hone] using (lOneOrderUnitEquiv_le_iff e he _ _).mpr hb.1
  · simpa only [map_smul, hone] using (lOneOrderUnitEquiv_le_iff e he _ _).mpr hb.2

def lOneOrderUnitLInfinityMap (f : Lp ℝ ∞ μ) : Lp ℝ ∞ ν :=
  (MemLp.of_bound (Lp.memLp (e (linftyToL1 μ f))).1 ‖f‖
    (lOneOrderUnitEquiv_bound e he hone f)).toLp (e (linftyToL1 μ f))

theorem lOneOrderUnitLInfinityMap_coe (f : Lp ℝ ∞ μ) :
    lOneOrderUnitLInfinityMap e he hone f =ᵐ[ν] e (linftyToL1 μ f) := MemLp.coeFn_toLp _

theorem linftyToL1_lOneOrderUnitLInfinityMap (f : Lp ℝ ∞ μ) :
    linftyToL1 ν (lOneOrderUnitLInfinityMap e he hone f) = e (linftyToL1 μ f) := by
  apply Lp.ext
  exact (linftyToL1_coe ν _).trans (lOneOrderUnitLInfinityMap_coe e he hone f)

theorem lOneOrderUnitLInfinityMap_norm_le (f : Lp ℝ ∞ μ) :
    ‖lOneOrderUnitLInfinityMap e he hone f‖ ≤ ‖f‖ := by
  apply linfty_norm_le_of_ae_bound _ (norm_nonneg f)
  filter_upwards [lOneOrderUnitLInfinityMap_coe e he hone f,
    lOneOrderUnitEquiv_bound e he hone f] with y hy hb
  simpa only [hy] using hb

include he in
theorem lOneOrderUnitEquiv_symm_nonneg (f : Lp ℝ 1 ν) : 0 ≤ e.symm f ↔ 0 ≤ f := by
  simpa only [e.apply_symm_apply] using (he (e.symm f)).symm

include hone in
theorem lOneOrderUnitEquiv_symm_one : e.symm (lOneUnit ν) = lOneUnit μ := by
  rw [← hone, e.symm_apply_apply]

theorem lOneOrderUnitLInfinityMap_inverse (f : Lp ℝ ∞ μ) :
    lOneOrderUnitLInfinityMap e.symm (lOneOrderUnitEquiv_symm_nonneg e he)
      (lOneOrderUnitEquiv_symm_one e hone) (lOneOrderUnitLInfinityMap e he hone f) = f := by
  apply linftyToL1_injective μ
  rw [linftyToL1_lOneOrderUnitLInfinityMap, linftyToL1_lOneOrderUnitLInfinityMap,
    e.symm_apply_apply]

theorem lOneOrderUnitLInfinityMap_norm (f : Lp ℝ ∞ μ) :
    ‖lOneOrderUnitLInfinityMap e he hone f‖ = ‖f‖ := by
  apply le_antisymm (lOneOrderUnitLInfinityMap_norm_le e he hone f)
  have h := lOneOrderUnitLInfinityMap_norm_le e.symm (lOneOrderUnitEquiv_symm_nonneg e he)
    (lOneOrderUnitEquiv_symm_one e hone) (lOneOrderUnitLInfinityMap e he hone f)
  rwa [lOneOrderUnitLInfinityMap_inverse] at h

def lOneOrderUnitLInfinityIsometry : Lp ℝ ∞ μ →ₗᵢ[ℝ] Lp ℝ ∞ ν where
  toFun := lOneOrderUnitLInfinityMap e he hone
  map_add' f g := by
    apply linftyToL1_injective ν
    rw [map_add, linftyToL1_lOneOrderUnitLInfinityMap, map_add, map_add,
      linftyToL1_lOneOrderUnitLInfinityMap, linftyToL1_lOneOrderUnitLInfinityMap]
  map_smul' c f := by
    apply linftyToL1_injective ν
    rw [map_smul, linftyToL1_lOneOrderUnitLInfinityMap, map_smul, map_smul,
      linftyToL1_lOneOrderUnitLInfinityMap]
    rfl
  norm_map' := lOneOrderUnitLInfinityMap_norm e he hone

theorem lOneOrderUnitLInfinityMap_surjective : Function.Surjective
    (lOneOrderUnitLInfinityIsometry e he hone) := by
  intro g
  refine ⟨lOneOrderUnitLInfinityMap e.symm (lOneOrderUnitEquiv_symm_nonneg e he)
    (lOneOrderUnitEquiv_symm_one e hone) g, ?_⟩
  apply linftyToL1_injective ν
  change linftyToL1 ν (lOneOrderUnitLInfinityMap e he hone _) = _
  rw [linftyToL1_lOneOrderUnitLInfinityMap, linftyToL1_lOneOrderUnitLInfinityMap,
    e.apply_symm_apply]

def lOneOrderUnitLInfinityEquiv : Lp ℝ ∞ μ ≃ₗᵢ[ℝ] Lp ℝ ∞ ν :=
  LinearIsometryEquiv.ofSurjective (lOneOrderUnitLInfinityIsometry e he hone)
    (lOneOrderUnitLInfinityMap_surjective e he hone)

theorem lOneOrderUnitLInfinityEquiv_nonneg (f : Lp ℝ ∞ μ) :
    0 ≤ lOneOrderUnitLInfinityEquiv e he hone f ↔ 0 ≤ f := by
  change 0 ≤ lOneOrderUnitLInfinityMap e he hone f ↔ 0 ≤ f
  rw [← linftyToL1_nonneg ν, linftyToL1_lOneOrderUnitLInfinityMap, he, linftyToL1_nonneg]

theorem lOneOrderUnitLInfinityEquiv_one :
    lOneOrderUnitLInfinityEquiv e he hone (linftyOne μ) = linftyOne ν := by
  apply linftyToL1_injective ν
  change linftyToL1 ν (lOneOrderUnitLInfinityMap e he hone _) = _
  rw [linftyToL1_lOneOrderUnitLInfinityMap, linftyToL1_one, linftyToL1_one, hone]

end ThesisCommon
