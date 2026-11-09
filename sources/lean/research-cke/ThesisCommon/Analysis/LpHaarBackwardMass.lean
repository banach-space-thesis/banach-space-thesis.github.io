import ThesisCommon.Analysis.LpHaarPartialLevels
import ThesisCommon.Analysis.LebesgueLpSupportedNorm

/-! The total mass of the raw Haar coefficients of an L1 function tends
to zero with the dyadic level. This supplies the backward interactions in
the successive faithful-block construction without an Lp-duality theorem. -/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜]

theorem lpHaarLevelProjection_L1_norm (n : ℕ) (f : IntervalLp 𝕜 ⟨1, le_rfl⟩) :
    ‖lpHaarLevelProjection 𝕜 ⟨1, le_rfl⟩ n f‖ =
      ∑ k : Fin (2 ^ n), intervalLpDyadicRadius n *
        ‖lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f‖ := by
  let A := lebesgueLpPartitionEquiv (𝕜 := 𝕜) (E := 𝕜) (p := 1) (by simp)
    (fun k : Fin (2 ^ n) => lpHaarCell n k) (fun _ => measurableSet_Ioc)
    (lpHaarLevelCells_disjoint n) (lpHaarLevelCells_cover n)
  rw [← A.norm_map (lpHaarLevelProjection 𝕜 ⟨1, le_rfl⟩ n f)]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    (A (lpHaarLevelProjection 𝕜 ⟨1, le_rfl⟩ n f))
  simp only [ENNReal.toReal_one, Real.rpow_one, tsum_fintype] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  change ‖lebesgueLpRestrict (𝕜 := 𝕜) (lpHaarCell n k)
    (lpHaarLevelProjection 𝕜 ⟨1, le_rfl⟩ n f)‖ = _
  rw [lpHaarLevelProjection_restrict_parent, norm_smul,
    lebesgueLpRestrict_norm_of_supported (lpHaarCell n k) measurableSet_Ioc
      (lpHaarDyadic 𝕜 ⟨1, le_rfl⟩ n k) (lpHaarDyadic_zero_off 𝕜 ⟨1, le_rfl⟩ n k),
    lpHaarDyadic_norm 𝕜 ⟨1, le_rfl⟩ (by simp) n k k.isLt]
  simp [mul_comm]

theorem lpHaar_L1_backward_mass_tendsto_zero (f : IntervalLp 𝕜 ⟨1, le_rfl⟩) :
    Tendsto (fun n => ∑ k : Fin (2 ^ n), intervalLpDyadicRadius n *
      ‖lpHaarDyadicCoefficient 𝕜 ⟨1, le_rfl⟩ n k f‖) atTop (𝓝 0) := by
  simpa only [← lpHaarLevelProjection_L1_norm, norm_zero] using
    (lpHaarLevelProjection_tendsto_zero 𝕜 ⟨1, le_rfl⟩ (by simp) f).norm

end ThesisCommon
