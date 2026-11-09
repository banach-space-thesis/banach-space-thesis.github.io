import SurveyStatements.P5L1VariationCellDensity
import SurveyStatements.P5L1VariationLocalCellTrace
import SurveyStatements.P5Support.LpHaarDiagonalBounds

/-! The local L¹ trace density for an arbitrary actual mean-zero operator.
Finite Reynolds eigenoperators prove full local limits; weak compactness
and actual dyadic means represent all of them by one L∞ function. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5L1Variation
open SurveyStatements.P5Support

def arbitraryLocalTraceValue (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) : 𝕜 :=
  Classical.choose (arbitrary_operator_local_average_limit 𝕜 R r root).2.2

theorem arbitraryLocalTraceValue_norm_le (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    ‖arbitraryLocalTraceValue 𝕜 R r root‖ ≤ 2 * ‖R‖ :=
  (Classical.choose_spec (arbitrary_operator_local_average_limit 𝕜 R r root).2.2).1

theorem arbitraryLocalTraceValue_tendsto (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) (r : ℕ) (root : Fin (2 ^ r)) :
    Tendsto (fun n => lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) n
      (lpHaarCell r root)) atTop
        (𝓝 ((intervalLpDyadicRadius r : 𝕜) * arbitraryLocalTraceValue 𝕜 R r root)) := by
  have hlim := (Classical.choose_spec (arbitrary_operator_local_average_limit 𝕜 R r root).2.2).2
  apply (tendsto_add_atTop_iff_nat r).mp
  have hformula (j : ℕ) := operator_levelTrace_cell_eq_average 𝕜 R (r + j) r (by omega) root
  simpa only [Nat.add_comm, hformula] using tendsto_const_nhds.mul hlim

theorem arbitrary_operator_full_cell_trace_Linfty_density (𝕜 : Type*) [RCLike 𝕜]
    (R : MeanZeroL1 𝕜 →L[𝕜] MeanZeroL1 𝕜) :
    ∃ m : IntervalLinfty 𝕜, ‖m‖ ≤ 2 * ‖R‖ ∧
      (∀ (r : ℕ) (root : Fin (2 ^ r)),
        (∫ x in lpHaarCell r root, m x ∂(volume.restrict (Icc (0 : ℝ) 1))) =
        (intervalLpDyadicRadius r : 𝕜) * arbitraryLocalTraceValue 𝕜 R r root) ∧
      ∀ (r : ℕ) (root : Fin (2 ^ r)),
        Tendsto (fun n => lpHaarLevelTrace (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) n
        (lpHaarCell r root)) atTop
          (𝓝 (∫ x in lpHaarCell r root, m x ∂(volume.restrict (Icc (0 : ℝ) 1)))) := by
  have hd (n : ℕ) (k : Fin (2 ^ n)) :
      ‖haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R) n k‖ ≤ 12 * ‖R‖ := by
    have h := lpHaar_operator_diagonal_norm_le 𝕜 ⟨1, le_rfl⟩ (by norm_num) (extendMeanZero 𝕜 R) n k
    have hn := extendMeanZero_norm_le 𝕜 R
    dsimp [haarOperatorDiagonal]
    linarith
  obtain ⟨m, hm, hint⟩ := exists_Linfty_of_full_cell_traces 𝕜
    (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 R)) (arbitraryLocalTraceValue 𝕜 R)
    (12 * ‖R‖) (2 * ‖R‖) (by positivity) (by positivity) hd
    (arbitraryLocalTraceValue_norm_le 𝕜 R) (arbitraryLocalTraceValue_tendsto 𝕜 R)
  refine ⟨m, hm, hint, ?_⟩
  intro r root
  rw [hint]
  exact arbitraryLocalTraceValue_tendsto 𝕜 R r root

end SurveyStatements.P5L1Variation
