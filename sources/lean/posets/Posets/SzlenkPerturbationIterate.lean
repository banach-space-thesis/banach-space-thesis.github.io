import Posets.SzlenkPerturbation

/-! Compact perturbations remain close at every derivative stage. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem weakStar_norm_sub_right_isClosed (x : WeakDual 𝕜 E) (δ : ℝ) :
    IsClosed {y : WeakDual 𝕜 E |
      ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤ δ} := by
  let f : WeakDual 𝕜 E → WeakDual 𝕜 E × WeakDual 𝕜 E := fun y => (x, y)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  exact (weakStar_norm_sub_isClosed (𝕜 := 𝕜) (E := E) δ).preimage hf

theorem szlenkIterate_perturbation {ε η δ : ℝ} {K L : Set (WeakDual 𝕜 E)}
    (hL : IsCompact L) (hscale : η + 2 * δ ≤ ε / 2)
    (hnear : ∀ a ∈ K, ∃ b ∈ L,
      ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ δ)
    (α : Ordinal) :
    ∀ x ∈ szlenkIterate ε K α, ∃ y ∈ szlenkIterate η L α,
      ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤ δ := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
      obtain rfl := hα.eq_bot
      simpa only [Ordinal.bot_eq_zero, szlenkIterate_zero] using hnear
  | succ α hα ih =>
      simp only [szlenkIterate_succ]
      intro x hx
      exact szlenkDeriv_perturbation (szlenkIterate_isCompact η hL α) hscale ih hx
  | isSuccLimit α hα ih =>
      intro x hx
      letI : Nonempty (Set.Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
      let A : Set.Iio α → Set (WeakDual 𝕜 E) := fun β =>
        szlenkIterate η L β.val ∩
          {y | ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤ δ}
      have hAn : ∀ β, (A β).Nonempty := by
        intro β
        have hxβ := szlenkIterate_antitone ε K β.property.le hx
        obtain ⟨y, hy, hdist⟩ := ih β.val β.property x hxβ
        exact ⟨y, hy, hdist⟩
      have hAc : ∀ β, IsCompact (A β) := fun β =>
        (szlenkIterate_isCompact η hL β.val).inter_right
          (weakStar_norm_sub_right_isClosed x δ)
      have hAd : Directed (· ⊇ ·) A := by
        intro β γ
        refine ⟨max β γ, ?_, ?_⟩
        · exact inter_subset_inter_left _ (szlenkIterate_antitone η L (le_max_left β γ))
        · exact inter_subset_inter_left _ (szlenkIterate_antitone η L (le_max_right β γ))
      obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        A hAd hAn hAc (fun β => (hAc β).isClosed)
      refine ⟨y, ?_, (mem_iInter.mp hy ⟨0, hα.bot_lt⟩).2⟩
      rw [szlenkIterate_limit η L α hα]
      exact mem_iInter.mpr (fun β => (mem_iInter.mp hy β).1)

end Posets
