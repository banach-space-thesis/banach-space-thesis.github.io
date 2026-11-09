import ThesisCommon.Analysis.LpCompactCoordinates
import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.BanachAdjointNorm

/-! LPCK Lemma 3.1 for every actual finite-p sum. The hypothesis is exactly
the source's compactness hypothesis for scalar-valued operators. The diagonal
scalarisation is constructed using the Hahn--Banach adjoint norm equality. -/
noncomputable section
open scoped ENNReal Topology
open Filter
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem exists_norming_postcomposition (T : X →L[𝕜] Y) :
    ∃ f : Y →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧ ‖T‖ ≤ 2 * ‖f.comp T‖ := by
  by_cases hT : T = 0
  · exact ⟨0, by simp, by simp [hT]⟩
  have hpos : 0 < ‖T‖ := norm_pos_iff.mpr hT
  obtain ⟨f, hf, hbound⟩ := (banachAdjoint T).exists_lt_apply_of_lt_opNorm
    (r := ‖T‖/2) (by rw [norm_banachAdjoint]; linarith)
  refine ⟨f, hf.le, ?_⟩
  change ‖T‖/2 < ‖f.comp T‖ at hbound
  linarith

theorem lp_coordinate_norm_tendsto_zero_of_scalar_compact
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hcompact : ∀ S : X →L[𝕜] lp (fun _ : ℕ => 𝕜) p, IsCompactOperator S)
    (T : X →L[𝕜] lp (fun _ : ℕ => Y) p) :
    Tendsto (fun n => ‖(lpCoordinate p n).comp T‖) atTop (𝓝 0) := by
  choose f hf hnorm using fun n => exists_norming_postcomposition ((lpCoordinate p n).comp T)
  let D := lpDiagonal p f 1 zero_le_one hf
  let S := D.comp T
  have hS := IsCompactOperator.lp_coordinate_norm_tendsto_zero hp (hcompact S)
  have heq : ∀ n, (lpCoordinate p n).comp S = (f n).comp ((lpCoordinate p n).comp T) := by
    intro n
    ext x
    rfl
  have hbound : ∀ n, ‖(lpCoordinate p n).comp T‖ ≤ 2 * ‖(lpCoordinate p n).comp S‖ := by
    intro n
    rw [heq]
    exact hnorm n
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa using hS.const_mul 2)

end ThesisCommon
