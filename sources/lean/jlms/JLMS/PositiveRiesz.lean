import JLMS.PositiveDecomposition
import JLMS.ScatteredMeasures
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Finite Riesz measures for positive bounded functionals

Restrict a positive functional on C₀(K,ℝ) to compactly supported functions,
apply mathlib's Riesz–Markov–Kakutani theorem, and bound the total mass by
the original operator norm using compact clopen cutoff functions.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Set MeasureTheory Topology
open scoped CompactlySupported ENNReal

namespace JLMS

variable {K : Type*} [TopologicalSpace K]

/-- Inclusion of compactly supported continuous functions in C₀(K). -/
def compactSupportInclusion : C_c(K, ℝ) →ₗ[ℝ] CZero ℝ K where
  toFun f := (f : CZero ℝ K)
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

@[simp] theorem compactSupportInclusion_apply (f : C_c(K, ℝ)) (x : K) :
    compactSupportInclusion f x = f x := rfl

/-- Restriction of a positive continuous functional to C_c(K). -/
def positiveFunctionalOnCC (φ : CZero ℝ K →L[ℝ] ℝ)
    (hφ : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ φ f) : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (φ.toLinearMap.comp compactSupportInclusion)
    (fun _ hf => hφ _ (fun x => hf x))

/-- A compact clopen indicator viewed as a compactly supported function. -/
def compactIndicatorCC (U : Set K) (hU : IsClopen U) (hc : IsCompact U) : C_c(K, ℝ) where
  toContinuousMap := (clopenIndicator U hU hc).toContinuousMap
  hasCompactSupport' := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hU.isClosed
    intro x hx
    by_contra hxU
    exact hx (by change clopenIndicator U hU hc x = 0; simp [hxU])

@[simp] theorem compactIndicatorCC_apply (U : Set K) (hU : IsClopen U)
    (hc : IsCompact U) (x : K) : compactIndicatorCC U hU hc x = if x ∈ U then 1 else 0 :=
  clopenIndicator_apply U hU hc x

@[simp] theorem compactSupportInclusion_indicator (U : Set K) (hU : IsClopen U)
    (hc : IsCompact U) : compactSupportInclusion (compactIndicatorCC U hU hc) =
      clopenIndicator U hU hc := by ext x; rfl

variable [LocallyCompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

/-- The Riesz measure of a positive bounded C₀ functional has mass bounded
by its norm. No σ-compactness or countable base is assumed. -/
theorem positiveRiesz_mass_le (hK : IsScattered K) (φ : CZero ℝ K →L[ℝ] ℝ)
    (hφ : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ φ f) :
    RealRMK.rieszMeasure (positiveFunctionalOnCC φ hφ) univ ≤ ENNReal.ofReal ‖φ‖ := by
  let Λ := positiveFunctionalOnCC φ hφ
  let μ := RealRMK.rieszMeasure Λ
  letI : μ.Regular := by dsimp [μ, RealRMK.rieszMeasure]; infer_instance
  change μ univ ≤ _
  rw [isOpen_univ.measure_eq_iSup_isCompact μ]
  refine iSup_le fun C => iSup_le fun _ => iSup_le fun hC => ?_
  obtain ⟨U, hU, hc, hCU⟩ := exists_compact_clopen_superset hK hC
  have hn : Λ (compactIndicatorCC U hU hc) ≤ ‖φ‖ := by
    change φ (compactSupportInclusion (compactIndicatorCC U hU hc)) ≤ _
    rw [compactSupportInclusion_indicator]
    exact (le_abs_self _).trans ((φ.le_opNorm _).trans
      (by simpa using (mul_le_mul_of_nonneg_left
        (norm_clopenIndicator_le (𝕜 := ℝ) U hU hc) (norm_nonneg φ))))
  exact (RealRMK.rieszMeasure_le_of_eq_one Λ
    (fun x => by simp only [compactIndicatorCC_apply]; split_ifs <;> norm_num)
    hC (fun x hx => by simp [hCU hx])).trans (ENNReal.ofReal_le_ofReal hn)

/-- A positive C₀ functional yields a finite regular measure, representing
it on every compactly supported test function. -/
theorem exists_finite_regular_positiveRiesz (hK : IsScattered K)
    (φ : CZero ℝ K →L[ℝ] ℝ) (hφ : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ φ f) :
    ∃ μ : Measure K, IsFiniteMeasure μ ∧ μ.Regular ∧
      μ univ ≤ ENNReal.ofReal ‖φ‖ ∧
      ∀ f : C_c(K, ℝ), ∫ x, f x ∂μ = φ (compactSupportInclusion f) := by
  let μ := RealRMK.rieszMeasure (positiveFunctionalOnCC φ hφ)
  have hm := positiveRiesz_mass_le hK φ hφ
  refine ⟨μ, ⟨hm.trans_lt ENNReal.ofReal_lt_top⟩, ?_, hm, ?_⟩
  · dsimp [μ, RealRMK.rieszMeasure]; infer_instance
  · intro f
    exact RealRMK.integral_rieszMeasure (positiveFunctionalOnCC φ hφ) f

end JLMS
