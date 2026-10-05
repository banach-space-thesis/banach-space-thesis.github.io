import ThesisCommon.Analysis.ExtendedReciprocalProfile
import Mathlib.Analysis.Convex.Piecewise

/-! Gluing the identity below one to a concave function above one. The
right-hand function lies below the identity and agrees with it at one;
these conditions supply the necessary slope inequality at the join. -/
noncomputable section
namespace ThesisCommon

theorem concaveOn_Ici_antitone_of_nonpos {F : ℝ → ℝ}
    (hF : ConcaveOn ℝ (Set.Ici 1) F) (hF1 : F 1 = 0)
    (hneg : ∀ x, 1 ≤ x → F x ≤ 0) : AntitoneOn F (Set.Ici 1) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  rcases (show 1 ≤ x from hx).eq_or_lt with rfl | hx1
  · simpa only [hF1] using hneg y hy
  have hs := hF.slope_anti_adjacent (x := 1) (y := x) (z := y) (by simp) hy hx1 hxy
  rw [hF1, sub_zero] at hs
  have hr : F x / (x - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (hneg x hx) (by linarith)
  have hh := (div_le_iff₀ (sub_pos.mpr hxy)).mp (hs.trans hr)
  linarith

theorem concaveOn_identity_extension {U : ℝ → ℝ}
    (hU : ConcaveOn ℝ (Set.Ici 1) U) (hU1 : U 1 = 1)
    (hle : ∀ x, 1 ≤ x → U x ≤ x) :
    ConcaveOn ℝ Set.univ (fun x => if x ≤ 1 then x else U x) := by
  let F : ℝ → ℝ := fun x => U x - x
  have hF : ConcaveOn ℝ (Set.Ici 1) F := hU.sub (convexOn_id (convex_Ici 1))
  have hF1 : F 1 = 0 := by simp [F, hU1]
  have hFa : AntitoneOn F (Set.Ici 1) := concaveOn_Ici_antitone_of_nonpos hF hF1
    (fun x hx => sub_nonpos.mpr (hle x hx))
  have hpiece := concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici
    (concaveOn_const (c := (0 : ℝ)) (convex_Iic 1)) hF
    (fun _ _ _ _ _ => le_rfl) hFa hF1.symm
  have hsum := hpiece.add (concaveOn_id (convex_univ : Convex ℝ (Set.univ : Set ℝ)))
  convert hsum using 1
  funext x
  simp only [Pi.add_apply, Set.piecewise, Set.mem_Iic, id_eq]
  split_ifs <;> simp [F]

theorem extendedReciprocalProfile_concaveOn {β : ℝ → ℝ}
    (hβ : ∀ x, 1 ≤ x → 1 ≤ β x) (hβ1 : β 1 = 1)
    (hconc : ConcaveOn ℝ (Set.Ici 1) (fun x => x / β x)) :
    ConcaveOn ℝ (Set.Ici 0) (extendedReciprocalProfile β) := by
  have hc := concaveOn_identity_extension hconc (by simp [hβ1])
    (fun x hx => div_le_self (zero_le_one.trans hx) (hβ x hx))
  exact hc.subset (Set.subset_univ _) (convex_Ici 0)

end ThesisCommon
