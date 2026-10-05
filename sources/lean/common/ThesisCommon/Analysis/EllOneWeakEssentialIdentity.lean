import ThesisCommon.Analysis.RCLikeEllOneWeakCompact
import ThesisCommon.Analysis.LpCompactCoordinates
import ThesisCommon.Analysis.WeakEssentialNormProperties

/-! The actual weak essential norm of the identity on scalar ℓ¹ is one.
Weakly compact images have compact norm closure by Schur's theorem, and
their coordinates therefore vanish uniformly. Testing a late unit vector
gives the sharp lower bound, over both real and complex scalars. -/
noncomputable section
open Set Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem IsWeaklyCompactOperator.scalarEllOne_coordinates_uniformly_small
    {W : E →L[𝕜] lp (fun _ : ℕ => 𝕜) 1} (hW : IsWeaklyCompactOperator W)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : E, ‖x‖ ≤ 1 → ‖W x n‖ < ε := by
  obtain ⟨K, hK, hWK⟩ := hW
  have hcompact := isCompact_norm_of_weakScalarEllOne hK
  filter_upwards [IsCompact.lp_coordinates_uniformly_small (by simp) hcompact hε] with n hn
  intro x hx
  exact hn (W x) ⟨toWeakSpace 𝕜 _ (W x), hWK x hx, by simp⟩

theorem one_le_norm_id_sub_weaklyCompact_scalarEllOne
    {W : lp (fun _ : ℕ => 𝕜) 1 →L[𝕜] lp (fun _ : ℕ => 𝕜) 1}
    (hW : IsWeaklyCompactOperator W) :
    1 ≤ ‖ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1) - W‖ := by
  by_contra h
  have hε : 0 < (1 - ‖ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1) - W‖) / 2 := by
    linarith
  obtain ⟨n, hn⟩ := (hW.scalarEllOne_coordinates_uniformly_small hε).exists
  let e : lp (fun _ : ℕ => 𝕜) 1 := lp.single 1 n 1
  have he : ‖e‖ = 1 := by simp [e, lp.norm_single (by simp : (0 : ENNReal) < 1)]
  have hsmall := hn e he.le
  let R := ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1) - W
  have hcoord : ‖(1 : 𝕜) - W e n‖ ≤
      ‖ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1) - W‖ := by
    calc
      ‖(1 : 𝕜) - W e n‖ = ‖(R e) n‖ := by simp [R, e]
      _ ≤ ‖R e‖ := lp.norm_apply_le_norm (by simp) _ n
      _ ≤ ‖R‖ * ‖e‖ := R.le_opNorm e
      _ = ‖ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1) - W‖ := by rw [he, mul_one]
  have htri := norm_le_norm_sub_add (1 : 𝕜) (W e n)
  rw [norm_one] at htri
  linarith

theorem weakEssentialNorm_id_scalarEllOne :
    weakEssentialNorm (ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1)) = 1 := by
  apply le_antisymm ((weakEssentialNorm_le_norm _).trans ContinuousLinearMap.norm_id_le)
  apply le_csInf
  · exact ⟨‖ContinuousLinearMap.id 𝕜 (lp (fun _ : ℕ => 𝕜) 1) - 0‖,
      0, weaklyCompact_zero, rfl⟩
  · rintro r ⟨W, hW, rfl⟩
    exact one_le_norm_id_sub_weaklyCompact_scalarEllOne hW

end ThesisCommon
