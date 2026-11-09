import SurveyStatements.P5OperatorReductionJointReaders
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Norming readers of actual disjoint L1 restrictions. Hahn--Banach
provides their scalar functionals without any unproved L1-dual identification.
The simultaneous variation bound follows from disjoint set integrals. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5
variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_l1_restriction (s : Set ℝ) (hs : MeasurableSet s)
    (f : Lp 𝕜 1 unitIntervalMeasure) :
    ‖vectorIndicatorMultiply (𝕜 := 𝕜) s hs f‖ =
      ∫ x in s, ‖f x‖ ∂unitIntervalMeasure := by
  rw [L1.norm_eq_integral_norm]
  have hnormae := (vectorIndicatorMultiply_ae (𝕜 := 𝕜) s hs f).fun_comp norm
  change (fun x => ‖(vectorIndicatorMultiply (𝕜 := 𝕜) s hs f) x‖) =ᵐ[unitIntervalMeasure]
    fun x => ‖s.indicator f x‖ at hnormae
  rw [integral_congr_ae hnormae]
  have hpoint (x : ℝ) : ‖s.indicator f x‖ = s.indicator (fun x => ‖f x‖) x := by
    by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [hpoint]
  rw [integral_indicator hs]

def restrictedFunctional (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜) :
    Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜 :=
  φ.comp (vectorIndicatorMultiply (𝕜 := 𝕜) s hs)

theorem sum_norm_restrictedFunctional_le {ι : Type*} (F : Finset ι)
    (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (s i) (s j))
    (φ : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜)
    (hφ : ∀ i ∈ F, ‖φ i‖ ≤ 1) (f : Lp 𝕜 1 unitIntervalMeasure) :
    ∑ i ∈ F, ‖restrictedFunctional (s i) (hs i) (φ i) f‖ ≤ ‖f‖ := by
  have hf := ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)).norm
  calc
    _ ≤ ∑ i ∈ F, ‖vectorIndicatorMultiply (𝕜 := 𝕜) (s i) (hs i) f‖ :=
      Finset.sum_le_sum (fun i hi => by
        change ‖φ i (vectorIndicatorMultiply (𝕜 := 𝕜) (s i) (hs i) f)‖ ≤ _
        exact ((φ i).le_opNorm _).trans
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (hφ i hi) (norm_nonneg _)))
    _ = ∑ i ∈ F, ∫ x in s i, ‖f x‖ ∂unitIntervalMeasure := by
      simp_rw [norm_l1_restriction]
    _ = ∫ x in ⋃ i ∈ F, s i, ‖f x‖ ∂unitIntervalMeasure :=
      (integral_biUnion_finset F (fun i _ => hs i) hd
        (fun _ _ => hf.integrableOn)).symm
    _ ≤ ∫ x, ‖f x‖ ∂unitIntervalMeasure :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun x => norm_nonneg (f x))) hf
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

theorem exists_disjoint_norming_readers {ι : Type*} (F : Finset ι)
    (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (s i) (s j))
    (f : ι → Lp 𝕜 1 unitIntervalMeasure) :
    ∃ π : ι → Lp 𝕜 1 unitIntervalMeasure →L[𝕜] 𝕜,
      (∀ i, π i (f i) = (∫ x in s i, ‖f i x‖ ∂unitIntervalMeasure : ℝ)) ∧
      ∀ y : Lp 𝕜 1 unitIntervalMeasure, ∑ i ∈ F, ‖π i y‖ ≤ ‖y‖ := by
  choose φ hφ hnorm using (fun i => exists_dual_vector'' 𝕜
    (vectorIndicatorMultiply (𝕜 := 𝕜) (s i) (hs i) (f i)))
  refine ⟨fun i => restrictedFunctional (s i) (hs i) (φ i), ?_, ?_⟩
  · intro i
    change φ i (vectorIndicatorMultiply (𝕜 := 𝕜) (s i) (hs i) (f i)) = _
    rw [hnorm i, norm_l1_restriction]
  · intro y
    exact sum_norm_restrictedFunctional_le F s hs hd φ (fun i _ => hφ i) y

end SurveyStatements.P5OperatorReduction
