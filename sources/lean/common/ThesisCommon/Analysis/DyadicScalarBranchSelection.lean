import ThesisCommon.Analysis.DyadicBranchVariation

/-! A single full subtree and a single colour retain a scalar lower bound
and have summable variation on every branch. The limits keep the same lower
bound. This also applies to complex coefficients without ordering them. -/
noncomputable section
open Filter Topology
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def DyadicBranchControl (f : DyadicTreeNode → 𝕜) (e : DyadicSubtreeEmbedding)
    (a ε : ℝ) : Prop :=
  (∀ t, a ≤ ‖f (e t)‖) ∧
  ∀ u : DyadicTreeNode, ∀ b : ℕ → Bool, ∃ L : 𝕜,
    a ≤ ‖L‖ ∧ Tendsto (fun n => f (e (u ++ dyadicBranchPath b n))) atTop (𝓝 L) ∧
    Summable (fun n => ‖f (e (u ++ dyadicBranchPath b n)) - L‖) ∧
    (∑' n, ‖f (e (u ++ dyadicBranchPath b n)) - L‖) < ε

theorem exists_dyadic_scalar_branch_choice (F : Bool → DyadicTreeNode → 𝕜)
    (M : Bool → ℝ) (hM : ∀ c t, ‖F c t‖ ≤ M c) (a : ℝ)
    (hchoice : ∀ t, a ≤ ‖F true t‖ ∨ a ≤ ‖F false t‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Bool, ∃ e : DyadicSubtreeEmbedding, DyadicBranchControl (F c) e a ε := by
  classical
  obtain ⟨e, he⟩ := exists_monochromatic_dyadic_subtree {t | a ≤ ‖F true t‖}
  have hselect : ∃ c : Bool, ∀ t, a ≤ ‖F c (e t)‖ := by
    rcases he with he | he
    · exact ⟨true, he⟩
    · exact ⟨false, fun t => (hchoice (e t)).resolve_left (he t)⟩
  obtain ⟨c, hc⟩ := hselect
  obtain ⟨g, hg⟩ := exists_dyadic_scalar_subtree_branch_variation
    (fun t => F c (e t)) (M c) (fun t => hM c (e t)) hε
  refine ⟨c, e.comp g, fun t => hc (g t), ?_⟩
  intro u b
  obtain ⟨L, hL, hsum, hbound⟩ := hg u b
  exact ⟨L, ge_of_tendsto' hL.norm (fun n => hc (g (u ++ dyadicBranchPath b n))),
    hL, hsum, hbound⟩

end ThesisCommon
