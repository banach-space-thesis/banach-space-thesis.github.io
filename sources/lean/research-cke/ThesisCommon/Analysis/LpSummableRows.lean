import ThesisCommon.Analysis.LpSummableColumns

/-! Summable rows define an actual lp-valued operator. Applied to each
row's whole future-input tail, they give a bounded lower part even at infinity. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def lpSummableRows (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : ℕ → Y →L[𝕜] X) :
    Y →L[𝕜] lp (fun _ : ℕ => X) p :=
  ∑' j, (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j).comp (F j)

theorem norm_lpSummableRows_le (F : ℕ → Y →L[𝕜] X)
    (hF : Summable (fun j => ‖F j‖)) : ‖lpSummableRows p F‖ ≤ ∑' j, ‖F j‖ := by
  have hs : Summable (fun j => ‖(lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j).comp (F j)‖) :=
    hF.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => norm_comp_left_contraction _ (norm_lpSingleCLM_le j) _)
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum
    (fun j => norm_comp_left_contraction _ (norm_lpSingleCLM_le j) _) hF)

theorem lpSummableRows_apply [CompleteSpace X] (F : ℕ → Y →L[𝕜] X)
    (hF : Summable (fun j => ‖F j‖)) (x : Y) (k : ℕ) :
    lpSummableRows p F x k = F k x := by
  have hs : Summable (fun j => (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j).comp (F j)) :=
    hF.of_norm_bounded (fun j => norm_comp_left_contraction _ (norm_lpSingleCLM_le j) _)
  let ev : (Y →L[𝕜] lp (fun _ : ℕ => X) p) →L[𝕜] X :=
    (lpCoordinate p k).comp (ContinuousLinearMap.apply 𝕜 (lp (fun _ : ℕ => X) p) x)
  change ev (∑' j, (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) p j).comp (F j)) = _
  rw [ev.map_tsum hs, tsum_eq_single k]
  · simp [ev]
  · intro j hjk
    simp [ev, hjk.symm]

theorem exists_lp_lower_part_of_summable_tails [CompleteSpace X]
    (S : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    {δ : ℕ → ℝ} (hδ : Summable δ)
    (htail : ∀ j, ‖((lpCoordinate p j).comp S).comp
      (lpExtend p (coordinateTail (Function.Embedding.refl ℕ) j))‖ ≤ δ j) :
    ∃ L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p,
      ‖S-L‖ ≤ ∑' j, δ j ∧ IsLpLowerPart S L := by
  let s := fun j => coordinateTail (Function.Embedding.refl ℕ) j
  let F : ℕ → lp (fun _ : ℕ => X) p →L[𝕜] X := fun j =>
    (((lpCoordinate p j).comp S).comp (lpExtend p (s j))).comp (lpRestrict p (s j))
  have hbound : ∀ j, ‖F j‖ ≤ δ j := fun j =>
    (norm_comp_right_contraction _ _ (norm_lpRestrict_le (s j))).trans (htail j)
  have hF : Summable (fun j => ‖F j‖) := hδ.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  let H := lpSummableRows p F
  refine ⟨S-H, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using (norm_lpSummableRows_le F hF).trans
      (hF.tsum_le_tsum hbound hδ)
  · intro x k
    change S x k - H x k = S (lpPrefix k x) k
    rw [lpSummableRows_apply F hF]
    have h := congrArg (fun y : lp (fun _ : ℕ => X) p => S y k)
      (lpPrefix_add_tail (𝕜 := 𝕜) k x)
    simp only [map_add, lp.coeFn_add, Pi.add_apply] at h
    exact (eq_sub_of_add_eq h).symm

end ThesisCommon
