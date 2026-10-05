import Posets.SzlenkIdealComposition

/-! A local projection comparison for the actual Szlenk derivatives. This
is the mass-concentration step used for a varying c₀ sum. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem szlenkIterate_local_projection
    (p : WeakDual 𝕜 E → WeakDual 𝕜 F) (hp : Continuous p)
    {K U : Set (WeakDual 𝕜 E)} (hU : IsOpen U) {ε δ : ℝ}
    (hd : ∀ a ∈ K ∩ U, ∀ b ∈ K ∩ U,
      ε < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ →
        δ < ‖WeakDual.toStrongDual (p a) - WeakDual.toStrongDual (p b)‖)
    (α : Ordinal) :
    ∀ x ∈ szlenkIterate ε K α ∩ U, p x ∈ szlenkIterate δ (p '' K) α := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
      obtain rfl := hα.eq_bot
      intro x hx
      simp only [Ordinal.bot_eq_zero, szlenkIterate_zero] at hx ⊢
      exact ⟨x, hx.1, rfl⟩
  | succ α hα ih =>
      intro x hx
      rw [szlenkIterate_succ] at hx ⊢
      refine ⟨ih x ⟨hx.1.1, hx.2⟩, ?_⟩
      intro V hV hxV
      obtain ⟨a, ha, b, hb, hab⟩ := hx.1.2 (U ∩ p ⁻¹' V)
        (hU.inter (hV.preimage hp)) ⟨hx.2, hxV⟩
      exact ⟨p a, ⟨ih a ⟨ha.1, ha.2.1⟩, ha.2.2⟩,
        p b, ⟨ih b ⟨hb.1, hb.2.1⟩, hb.2.2⟩,
        hd a ⟨szlenkIterate_subset ε K α ha.1, ha.2.1⟩
          b ⟨szlenkIterate_subset ε K α hb.1, hb.2.1⟩ hab⟩
  | isSuccLimit α hα ih =>
      intro x hx
      rw [szlenkIterate_limit δ _ α hα]
      apply mem_iInter.mpr
      intro β
      exact ih β.val β.property x
        ⟨szlenkIterate_antitone ε K β.property.le hx.1, hx.2⟩

def szlenkDualBall (R : ℝ) : Set (WeakDual 𝕜 E) :=
  {φ | ‖WeakDual.toStrongDual φ‖ ≤ R}

theorem szlenkDualBall_isClosed (R : ℝ) :
    IsClosed (szlenkDualBall (𝕜 := 𝕜) (E := E) R) := by
  simpa only [szlenkDualBall, Metric.closedBall, dist_zero_right, Set.preimage_setOf_eq]
    using WeakDual.isClosed_closedBall (0 : StrongDual 𝕜 E) R

theorem szlenkIterate_ball_shrink_of_projections {κ : Ordinal} {ε : ℝ} (hε : 0 < ε) (R : ℝ)
    (hproj : ∀ x : WeakDual 𝕜 E, ∀ r : ℝ, r < ‖WeakDual.toStrongDual x‖ →
      ∃ p : WeakDual 𝕜 E → WeakDual 𝕜 F, Continuous p ∧
        r < ‖WeakDual.toStrongDual (p x)‖ ∧
        HasSzlenkBound (p '' szlenkDualBall R) κ ∧
        ∀ a b, ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤
          ‖WeakDual.toStrongDual (p a) - WeakDual.toStrongDual (p b)‖ +
          (‖WeakDual.toStrongDual a‖ - ‖WeakDual.toStrongDual (p a)‖) +
          (‖WeakDual.toStrongDual b‖ - ‖WeakDual.toStrongDual (p b)‖)) :
    szlenkIterate ε (szlenkDualBall (𝕜 := 𝕜) (E := E) R) κ ⊆
      szlenkDualBall (R - ε / 8) := by
  intro x hx
  change ‖WeakDual.toStrongDual x‖ ≤ R - ε / 8
  by_contra hn
  obtain ⟨p, hp, hpx, hbound, hdist⟩ := hproj x (R - ε / 8) (lt_of_not_ge hn)
  let U := p ⁻¹' (szlenkDualBall (𝕜 := 𝕜) (E := F) (R - ε / 8))ᶜ
  have hU : IsOpen U := (szlenkDualBall_isClosed _).isOpen_compl.preimage hp
  have hxU : x ∈ U := not_le.mpr hpx
  have hd : ∀ a ∈ szlenkDualBall R ∩ U, ∀ b ∈ szlenkDualBall R ∩ U,
      ε < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ →
        ε / 2 < ‖WeakDual.toStrongDual (p a) - WeakDual.toStrongDual (p b)‖ := by
    intro a ha b hb hab
    have haR : ‖WeakDual.toStrongDual a‖ ≤ R := ha.1
    have hbR : ‖WeakDual.toStrongDual b‖ ≤ R := hb.1
    have hap : R - ε / 8 < ‖WeakDual.toStrongDual (p a)‖ := lt_of_not_ge ha.2
    have hbp : R - ε / 8 < ‖WeakDual.toStrongDual (p b)‖ := lt_of_not_ge hb.2
    have hh := hdist a b
    linarith
  have hh := szlenkIterate_local_projection p hp hU hd κ x ⟨hx, hxU⟩
  rw [hbound (ε / 2) (half_pos hε)] at hh
  exact hh

end Posets
