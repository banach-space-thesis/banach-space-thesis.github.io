import ThesisCommon.Analysis.DyadicChainOscillation

/-! One colour and one strong subtree have uniform scalar lower bounds and
summable descendant oscillation. Antitone envelopes survive all later
strong subtree selections. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_dyadic_scalar_descendant_choice (F : Bool → DyadicTreeNode → 𝕜)
    (M : Bool → ℝ) (hM : ∀ c t, ‖F c t‖ ≤ M c) (a : ℝ)
    (hchoice : ∀ t, a ≤ ‖F true t‖ ∨ a ≤ ‖F false t‖)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ c : Bool, ∃ e : DyadicSubtreeEmbedding,
      (∀ t, a ≤ ‖F c (e t)‖) ∧
      ∀ s t, s.IsPrefix t → ‖F c (e s)-F c (e t)‖ ≤ δ s.length := by
  classical
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  obtain ⟨e, he⟩ := exists_monochromatic_dyadic_subtree {t | a ≤ ‖F true t‖}
  have hselect : ∃ c : Bool, ∀ t, a ≤ ‖F c (e t)‖ := by
    rcases he with he | he
    · exact ⟨true, he⟩
    · exact ⟨false, fun t => (hchoice (e t)).resolve_left (he t)⟩
  obtain ⟨c, hc⟩ := hselect
  have htotal : TotallyBounded (Set.range fun t => F c (e t)) :=
    (isCompact_closedBall (0 : 𝕜) (M c)).totallyBounded.subset (by
      rintro _ ⟨t, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hM c (e t))
  obtain ⟨g,hg⟩ := exists_dyadic_subtree_descendant_oscillation
    (fun t => F c (e t)) htotal δ hδ
  exact ⟨c, e.comp g, fun t => hc (g t), fun s t hst => by
    simpa only [dist_eq_norm] using (hg s t hst).le⟩

end ThesisCommon
