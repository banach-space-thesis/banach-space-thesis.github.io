import SurveyStatements.P5L1VariationBoundedSteps
import SurveyStatements.P5L1VariationLpBoundClosed

/-! A bounded full dyadic-cell trace has an actual L∞ density. Weak
Hilbert compactness identifies the cell integrals; strong convergence of
the genuine dyadic means transfers the sharper local cell bound. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support
local instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem L2_inner_cell_conj_integral (𝕜 : Type*) [RCLike 𝕜]
    (f : IntervalL2 𝕜) (n : ℕ) (k : Fin (2 ^ n)) :
    inner 𝕜 f (lpHaarCellVector 𝕜 ⟨2, by norm_num⟩ n k) =
      star (∫ x in lpHaarCell n k, f x ∂(volume.restrict (Icc (0 : ℝ) 1))) := by
  rw [← inner_conj_symm]
  have h : inner 𝕜 (lpHaarCellVector 𝕜 ⟨2, by norm_num⟩ n k) f =
      ∫ x in lpHaarCell n k, f x ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
    L2.inner_indicatorConstLp_one (s := lpHaarCell n k) measurableSet_Ioc
      (measure_ne_top _ _) f
  rw [h, starRingEnd_apply]

theorem exists_Linfty_of_full_cell_traces (𝕜 : Type*) [RCLike 𝕜]
    (d : (n : ℕ) → Fin (2 ^ n) → 𝕜) (values : (n : ℕ) → Fin (2 ^ n) → 𝕜)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : ∀ n k, ‖d n k‖ ≤ B) (hvalues : ∀ n k, ‖values n k‖ ≤ C)
    (htrace : ∀ (n : ℕ) (k : Fin (2 ^ n)),
      Tendsto (fun l => lpHaarLevelTrace d l (lpHaarCell n k)) atTop
      (𝓝 ((intervalLpDyadicRadius n : 𝕜) * values n k))) :
    ∃ m : IntervalLinfty 𝕜, ‖m‖ ≤ C ∧ ∀ (n : ℕ) (k : Fin (2 ^ n)),
      (∫ x in lpHaarCell n k, m x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        (intervalLpDyadicRadius n : 𝕜) * values n k := by
  obtain ⟨m₂, hm₂norm, hm₂⟩ := exists_hilbert_pairing_cluster 𝕜 (IntervalL2 𝕜)
    (stepSymbolL2 𝕜 d B hB hd) B (stepSymbolL2_norm_le 𝕜 d B hB hd)
  have hint (n : ℕ) (k : Fin (2 ^ n)) :
      (∫ x in lpHaarCell n k, m₂ x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        (intervalLpDyadicRadius n : 𝕜) * values n k := by
    have hlim : Tendsto (fun l => inner 𝕜 (stepSymbolL2 𝕜 d B hB hd l)
        (lpHaarCellVector 𝕜 ⟨2, by norm_num⟩ n k)) atTop
        (𝓝 (star ((intervalLpDyadicRadius n : 𝕜) * values n k))) := by
      simpa only [L2_inner_cell_conj_integral, stepSymbolL2_setIntegral] using (htrace n k).star
    have heq := hm₂ (lpHaarCellVector 𝕜 ⟨2, by norm_num⟩ n k) _ hlim
    rw [L2_inner_cell_conj_integral] at heq
    exact star_injective heq
  have hmeans (n : ℕ) : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖lpHaarDyadicMean 𝕜 ⟨2, by norm_num⟩ (by norm_num) n m₂ x‖ ≤ C := by
    have hall := ae_all_iff.mpr (fun k : Fin (2 ^ n) =>
      lpHaarDyadicMean_coe 𝕜 ⟨2, by norm_num⟩ (by norm_num) n m₂ k)
    filter_upwards [hall, lpHaarLevelCells_cover n] with x hx hcover
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hcover
    have hv := hx k hk
    rw [hint] at hv
    have hr : (intervalLpDyadicRadius n : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (intervalLpDyadicRadius_pos n).ne'
    rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul] at hv
    rw [hv]
    exact hvalues n k
  have hbound : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ‖m₂ x‖ ≤ C :=
    ae_norm_bound_of_tendsto_Lp (p := (2 : ℝ≥0∞))
      (fun n => lpHaarDyadicMean 𝕜 ⟨2, by norm_num⟩ (by norm_num) n m₂) m₂ C hmeans
      (lpHaarDyadicMean_tendsto 𝕜 ⟨2, by norm_num⟩ (by norm_num) m₂)
  have hmem : MemLp m₂ ∞ (volume.restrict (Icc (0 : ℝ) 1)) :=
    memLp_top_of_bound (Lp.memLp m₂).aestronglyMeasurable C hbound
  let m : IntervalLinfty 𝕜 := hmem.toLp m₂
  refine ⟨m, ?_, ?_⟩
  · calc
      ‖m‖ = (eLpNorm m₂ ∞ (volume.restrict (Icc (0 : ℝ) 1))).toReal := Lp.norm_toLp m₂ hmem
      _ ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono (by simp) (eLpNormEssSup_le_of_ae_bound hbound)
      _ = C := ENNReal.toReal_ofReal hC
  · intro n k
    rw [integral_congr_ae (ae_restrict_of_ae hmem.coeFn_toLp)]
    exact hint n k

end SurveyStatements.P5L1Variation
