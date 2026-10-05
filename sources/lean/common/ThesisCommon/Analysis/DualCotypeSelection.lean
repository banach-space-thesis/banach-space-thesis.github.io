import ThesisCommon.Analysis.DualCotypeForward
import ThesisCommon.Analysis.EllOneForwardSelection
import ThesisCommon.Analysis.EllOneBackwardSelection

/-! The recursive estimates behind the dual-cotype triangular reductions.
There are no inner-coordinate refinements: the generic fusion arguments are
specialized to identity maps on the coefficient space. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem HasFiniteCotype.dual_ellOne_forward_selection
    (h : HasFiniteCotype (X →L[𝕜] 𝕜))
    (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ Y) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ k,
      ‖((lpRestrict 1 (coordinateTail e k)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 (e k))))‖ < δ k := by
  have hforward : ∀ (S : X →L[𝕜] EllOneSum ℕ Y) (ε : ℝ), 0 < ε →
      ∃ a m : ℕ ↪ ℕ, ‖((lpRestrict 1 m).comp S).comp (ContinuousLinearMap.id 𝕜 X)‖ < ε := by
    intro S ε hε
    obtain ⟨m, hm⟩ := h.dual_ellOne_forward_reduction S hε
    exact ⟨Function.Embedding.refl ℕ, m, by simpa using hm⟩
  obtain ⟨e, _a, he, hs⟩ := ellOne_forward_selection (𝕜 := 𝕜) (X := X) (Y := Y)
    (fun _ => ContinuousLinearMap.id 𝕜 X) hforward T δ hδ
  exact ⟨e, he, fun k => by simpa using hs k⟩

theorem HasFiniteCotype.dual_ellOne_backward_selection
    (h : HasFiniteCotype (X →L[𝕜] 𝕜))
    (T : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ Y) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ e : ℕ ↪ ℕ, StrictMono e ∧ ∀ i j, i < j →
      ‖(lpCoordinate 1 (e i)).comp
        (T.comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 (e j)))‖ < δ i := by
  have hback : ∀ (ε M : ℝ), 0 < ε → 0 ≤ M → ∃ N : ℕ,
      ∀ S : X →L[𝕜] EllOneSum (Fin N) Y, ‖S‖ ≤ M →
        ∃ (i : Fin N) (a : ℕ ↪ ℕ),
          ‖((lpCoordinate 1 i).comp S).comp (ContinuousLinearMap.id 𝕜 X)‖ < ε := by
    intro ε M hε hM
    obtain ⟨N, hN⟩ := h.dual_ellOne_backward_width (Y := Y) hε hM
    refine ⟨N, ?_⟩
    intro S hS
    obtain ⟨i, hi⟩ := hN S hS
    exact ⟨i, Function.Embedding.refl ℕ, by simpa using hi⟩
  obtain ⟨e, _a, he, hs⟩ := ellOne_backward_selection (𝕜 := 𝕜) (X := X) (Y := Y)
    (fun _ => ContinuousLinearMap.id 𝕜 X) (fun _ => ContinuousLinearMap.norm_id_le)
    (fun _ _ => by simp) (fun _ _ _ _ => le_rfl) hback T δ hδ
  exact ⟨e, he, fun i j hij => by simpa using hs i j hij⟩

end ThesisCommon
