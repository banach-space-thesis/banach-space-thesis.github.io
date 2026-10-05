import ThesisCommon.Analysis.KernelSmallSetTests
import ThesisCommon.Analysis.KernelLebesgueDecomposition

/-! A small-set bound detects the whole singular mass together with a large-
value density tail. The singular support can depend on the input point:
the countable-algebra lemma has already removed a common exceptional set. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace ThesisCommon
variable {Y : Type*} [MeasurableSpace Y]
variable {ν σ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure σ]

omit [IsFiniteMeasure ν] in
theorem singular_add_density_mass_le_smallSet_bound
    (hs : σ ⟂ₘ ν) {k : Y → ℝ} (hi : Integrable k ν)
    (hk0 : ∀ y, 0 ≤ k y) {B : Set Y} (hB : MeasurableSet B) {δ C : ℝ}
    (hBδ : ν.real B < δ)
    (hbound : ∀ A : Set Y, MeasurableSet A → ν.real A < δ →
      (σ + ν.withDensity (fun y => ENNReal.ofReal (k y))).real A ≤ C) :
    σ.real univ + (∫ y in B, k y ∂ν) ≤ C := by
  let A := hs.nullSetᶜ ∪ B
  have hA : MeasurableSet A := hs.measurableSet_nullSet.compl.union hB
  have hν : ν A = ν B := by
    apply le_antisymm
    · exact (measure_union_le _ _).trans (by simp)
    · exact measure_mono subset_union_right
  have hσ : σ A = σ univ := by
    apply measure_of_measure_compl_eq_zero
    exact measure_mono_null (by dsimp [A]; intro y hy; simpa using (not_or.mp hy).1)
      hs.measure_nullSet
  letI : IsFiniteMeasure (ν.withDensity (fun y => ENNReal.ofReal (k y))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  have hmass := hbound A hA (by simpa only [measureReal_def, hν] using hBδ)
  rw [measureReal_add_apply, measureReal_def, hσ] at hmass
  have hdensity : (ν.withDensity (fun y => ENNReal.ofReal (k y))).real B =
      ∫ y in B, k y ∂ν := by
    rw [measureReal_def, withDensity_apply _ hB,
      ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
        (Eventually.of_forall hk0), ENNReal.toReal_ofReal]
    exact integral_nonneg hk0
  have hmono : (ν.withDensity (fun y => ENNReal.ofReal (k y))).real B ≤
      (ν.withDensity (fun y => ENNReal.ofReal (k y))).real A :=
    measureReal_mono subset_union_right
  rw [hdensity] at hmono
  exact (add_le_add_left hmono _).trans hmass

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated Y]
variable {μ : Measure X}

theorem ae_kernel_singular_tail_bound (κ : Kernel X Y) [IsFiniteKernel κ]
    {δ C M r : ℝ} (hr : 0 < r) (hMr : M / r < δ)
    (hmass : ∀ᵐ x ∂μ, (κ x).real univ ≤ M)
    (htest : ∀ B : Set Y, MeasurableSet B → ν.real B < δ →
      ∀ᵐ x ∂μ, (κ x).real B ≤ C) :
    ∀ᵐ x ∂μ, (kernelSingularPart κ ν x).real univ +
      (∫ y in {y | r ≤ kernelRealDensity κ ν (x, y)},
        kernelRealDensity κ ν (x, y) ∂ν) ≤ C := by
  filter_upwards [ae_kernel_smallSet_bound κ htest, hmass] with x hx hmassx
  have hk : Measurable (fun y => kernelRealDensity κ ν (x, y)) :=
    (measurable_kernelRealDensity κ ν).comp
    (measurable_const.prodMk measurable_id)
  have hi := integrable_kernelRealDensity_column κ ν x
  have hk0 := fun y => kernelRealDensity_nonneg κ ν (x, y)
  have htail := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hk0) hi r
  have hBδ : ν.real {y | r ≤ kernelRealDensity κ ν (x, y)} < δ := by
    have hcol := (integral_kernelRealDensity_column_le κ ν x).trans hmassx
    have hle : ν.real {y | r ≤ kernelRealDensity κ ν (x, y)} ≤ M / r :=
      (le_div_iff₀ hr).mpr (by nlinarith)
    exact hle.trans_lt hMr
  apply singular_add_density_mass_le_smallSet_bound
    (kernelSingularPart_mutuallySingular κ ν x) hi hk0
    (measurableSet_le measurable_const hk) hBδ
  intro A hA hδ
  rw [add_comm, ← kernel_lebesgue_decomposition κ ν x]
  exact hx A hA hδ

end ThesisCommon
