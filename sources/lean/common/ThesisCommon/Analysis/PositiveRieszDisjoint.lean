import ThesisCommon.Analysis.PositiveRieszOrder

/-! Lattice disjointness of positive continuous functionals is exactly mutual
singularity of their finite regular representing measures. -/
noncomputable section
open Set MeasureTheory
namespace ThesisCommon
open scoped PositiveOperatorOrder DualLattice
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

def continuousMapIntegralCLM (μ : Measure K) [IsFiniteMeasure μ] : C(K, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (continuousMap_integrable_finite μ f)
        (continuousMap_integrable_finite μ g)
      map_smul' := fun c f => integral_smul c f }
    (μ.real univ) (fun f => by
      simpa only [mul_comm] using norm_integral_le_of_norm_le_const
        (μ := μ) (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x))

theorem continuousMapIntegralCLM_nonneg (μ : Measure K) [IsFiniteMeasure μ] :
    0 ≤ continuousMapIntegralCLM μ := by
  apply (operator_nonneg_iff _).mpr
  intro f hf
  exact integral_nonneg hf

theorem continuousMapIntegralCLM_mono {μ ν : Measure K}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≤ ν) :
    continuousMapIntegralCLM μ ≤ continuousMapIntegralCLM ν := by
  apply (operator_le_iff _ _).mpr
  intro f hf
  exact integral_mono_measure h (Filter.Eventually.of_forall hf)
    (continuousMap_integrable_finite ν f)

theorem continuousMapIntegralCLM_positiveContinuousMapRiesz
    (φ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) :
    continuousMapIntegralCLM (positiveContinuousMapRiesz φ hφ) = φ := by
  ext f
  exact integral_positiveContinuousMapRiesz φ hφ f

theorem continuousMapIntegralCLM_eq_zero_iff (μ : Measure K) [IsFiniteMeasure μ] :
    continuousMapIntegralCLM μ = 0 ↔ μ = 0 := by
  constructor
  · intro h
    have he := congrArg (fun L : C(K, ℝ) →L[ℝ] ℝ => L 1) h
    have hr : μ.real univ = 0 := by simpa [continuousMapIntegralCLM] using he
    apply Measure.measure_univ_eq_zero.mp
    exact (ENNReal.toReal_eq_zero_iff (μ univ)).mp hr |>.resolve_right (measure_ne_top μ univ)
  · rintro rfl
    ext f
    simp [continuousMapIntegralCLM]

theorem positiveContinuousMapRiesz_mutuallySingular_iff
    (φ ψ : C(K, ℝ) →L[ℝ] ℝ) (hφ : 0 ≤ φ) (hψ : 0 ≤ ψ) :
    (positiveContinuousMapRiesz φ hφ).MutuallySingular (positiveContinuousMapRiesz ψ hψ) ↔
      φ ⊓ ψ = 0 := by
  let μ := positiveContinuousMapRiesz φ hφ
  let ν := positiveContinuousMapRiesz ψ hψ
  constructor
  · intro h
    have hp : 0 ≤ φ ⊓ ψ := le_inf hφ hψ
    have hμ : positiveContinuousMapRiesz (φ ⊓ ψ) hp ≤ μ :=
      (positiveContinuousMapRiesz_le_iff _ _ hp hφ).mpr inf_le_left
    have hν : positiveContinuousMapRiesz (φ ⊓ ψ) hp ≤ ν :=
      (positiveContinuousMapRiesz_le_iff _ _ hp hψ).mpr inf_le_right
    have hz := (Measure.MutuallySingular.self_iff _).mp (h.mono hμ hν)
    rw [← continuousMapIntegralCLM_positiveContinuousMapRiesz (φ ⊓ ψ) hp]
    exact (continuousMapIntegralCLM_eq_zero_iff _).mpr hz
  · intro h
    letI : IsFiniteMeasure (μ ⊓ ν) := isFiniteMeasure_of_le μ inf_le_left
    have hμ := continuousMapIntegralCLM_mono (μ := μ ⊓ ν) (ν := μ) inf_le_left
    have hν := continuousMapIntegralCLM_mono (μ := μ ⊓ ν) (ν := ν) inf_le_right
    rw [continuousMapIntegralCLM_positiveContinuousMapRiesz φ hφ] at hμ
    rw [continuousMapIntegralCLM_positiveContinuousMapRiesz ψ hψ] at hν
    have hz : continuousMapIntegralCLM (μ ⊓ ν) = 0 :=
      le_antisymm ((le_inf hμ hν).trans_eq h) (continuousMapIntegralCLM_nonneg _)
    have hm := (continuousMapIntegralCLM_eq_zero_iff _).mp hz
    exact Measure.mutuallySingular_iff_disjoint.mpr (disjoint_iff.mpr hm)

end ThesisCommon
