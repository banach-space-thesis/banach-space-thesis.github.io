import ThesisCommon.Analysis.LpUpperTriangularParts

/-! Summable column norms define a bounded operator on every lp. Applied
to whole future-output tails, this gives LPCK's upper-part construction. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lpSummableColumns (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : ℕ → X →L[𝕜] Y) :
    lp (fun _ : ℕ => X) p →L[𝕜] Y := ∑' j, (F j).comp (lpCoordinate p j)

theorem norm_lpSummableColumns_le (F : ℕ → X →L[𝕜] Y)
    (hF : Summable (fun j => ‖F j‖)) : ‖lpSummableColumns p F‖ ≤ ∑' j, ‖F j‖ := by
  have hs : Summable (fun j => ‖(F j).comp (lpCoordinate p j)‖) :=
    hF.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => norm_comp_right_contraction _ _ (norm_lpCoordinate_le p j))
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
    (fun j => norm_comp_right_contraction _ _ (norm_lpCoordinate_le p j)) hF)

theorem lpSummableColumns_single [CompleteSpace Y] (F : ℕ → X →L[𝕜] Y)
    (hF : Summable (fun j => ‖F j‖)) (j : ℕ) (x : X) :
    lpSummableColumns p F (lp.single p j x) = F j x := by
  have hs : Summable (fun k => (F k).comp (lpCoordinate p k)) :=
    hF.of_norm_bounded (fun k => norm_comp_right_contraction _ _ (norm_lpCoordinate_le p k))
  let ev := ContinuousLinearMap.apply 𝕜 Y (lp.single (E := fun _ : ℕ => X) p j x)
  change ev (∑' k, (F k).comp (lpCoordinate p k)) = _
  rw [ev.map_tsum hs, tsum_eq_single j]
  · simp [ev]
  · intro k hkj
    simp [ev, hkj]

theorem exists_lp_upper_part_of_summable_tails [CompleteSpace X]
    (S : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    {δ : ℕ → ℝ} (hδ : Summable δ)
    (htail : ∀ j, ‖((lpRestrict p (coordinateTail (Function.Embedding.refl ℕ) j)).comp S).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j)‖ ≤ δ j) :
    ∃ U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p,
      ‖S-U‖ ≤ ∑' j, δ j ∧ IsLpUpperPart S U := by
  let s := fun j => coordinateTail (Function.Embedding.refl ℕ) j
  let F : ℕ → X →L[𝕜] lp (fun _ : ℕ => X) p := fun j => (lpExtend p (s j)).comp
    (((lpRestrict p (s j)).comp S).comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j))
  have hbound : ∀ j, ‖F j‖ ≤ δ j := fun j =>
    (norm_comp_left_contraction _ (norm_lpExtend_le (s j)) _).trans (htail j)
  have hF : Summable (fun j => ‖F j‖) := hδ.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  let H := lpSummableColumns p F
  refine ⟨S-H, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using (norm_lpSummableColumns_le F hF).trans
      (hF.tsum_le_tsum hbound hδ)
  · intro j x
    change S (lp.single p j x) - H (lp.single p j x) = _
    rw [lpSummableColumns_single F hF]
    exact (eq_sub_of_add_eq (lpPrefix_add_tail (𝕜 := 𝕜) j (S (lp.single p j x)))).symm

end ThesisCommon
