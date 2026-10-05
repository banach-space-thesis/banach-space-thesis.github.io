import Posets.SzlenkOperator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Compact weak-star images and the Szlenk derivation. The factor two in
the scale comparison permits many points in a compact fiber. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem szlenkDeriv_image_subset
    (f : WeakDual 𝕜 E → WeakDual 𝕜 F) (hf : Continuous f)
    {L δ ε : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ a b, ‖WeakDual.toStrongDual (f a) - WeakDual.toStrongDual (f b)‖ ≤
      L * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖)
    (hδε : 2 * L * δ ≤ ε) {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K) :
    szlenkDeriv ε (f '' K) ⊆ f '' szlenkDeriv δ K := by
  classical
  intro x hx
  by_contra hxn
  let V : Set (WeakDual 𝕜 E) := ⋃ U ∈
    {U : Set (WeakDual 𝕜 E) | IsOpen U ∧ ∀ y ∈ K ∩ U,
      ‖WeakDual.toStrongDual (f y) - WeakDual.toStrongDual x‖ ≤ L * δ}, U
  have hV : IsOpen V := isOpen_biUnion (fun U hU => hU.1)
  have hfiber : ∀ y ∈ K, f y = x → y ∈ V := by
    intro y hy hfy
    have hyd : y ∉ szlenkDeriv δ K := fun hd => hxn ⟨y, hd, hfy⟩
    have hn : ¬ ∀ U : Set (WeakDual 𝕜 E), IsOpen U → y ∈ U →
        ∃ a ∈ K ∩ U, ∃ b ∈ K ∩ U,
          δ < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ :=
      fun h => hyd ⟨hy, h⟩
    push_neg at hn
    obtain ⟨U, hU, hyU, hsmall⟩ := hn
    refine mem_iUnion₂.mpr ⟨U, ⟨hU, ?_⟩, hyU⟩
    intro z hz
    rw [← hfy]
    exact (hfL z y).trans (mul_le_mul_of_nonneg_left (hsmall z hz y ⟨hy, hyU⟩) hL)
  have hclosed : IsClosed (f '' (K \ V)) := (hK.diff hV).image hf |>.isClosed
  have hxV : x ∈ (f '' (K \ V))ᶜ := by
    rintro ⟨y, hy, hfy⟩
    exact hy.2 (hfiber y hy.1 hfy)
  have hnear : ∀ a ∈ f '' K ∩ (f '' (K \ V))ᶜ,
      ‖WeakDual.toStrongDual a - WeakDual.toStrongDual x‖ ≤ L * δ := by
    rintro a ⟨⟨y, hy, rfl⟩, hya⟩
    have hyV : y ∈ V := by
      by_contra hn
      exact hya ⟨y, ⟨hy, hn⟩, rfl⟩
    obtain ⟨U, hU, hyU⟩ := mem_iUnion₂.mp hyV
    exact hU.2 y ⟨hy, hyU⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 _ hclosed.isOpen_compl hxV
  have ha' := hnear a ha
  have hb' := hnear b hb
  have hab' : ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ 2 * L * δ := by
    calc
      _ ≤ ‖WeakDual.toStrongDual a - WeakDual.toStrongDual x‖ +
          ‖WeakDual.toStrongDual x - WeakDual.toStrongDual b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * δ + L * δ := add_le_add ha' (by simpa only [norm_sub_rev] using hb')
      _ = 2 * L * δ := by ring
  exact (not_lt_of_ge (hab'.trans hδε)) hab

/-- The image comparison persists at every ordinal, with one fixed scale
loss throughout the iteration. Compactness is essential at limit stages. -/
theorem szlenkIterate_image_subset
    (f : WeakDual 𝕜 E → WeakDual 𝕜 F) (hf : Continuous f)
    {L δ ε : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ a b, ‖WeakDual.toStrongDual (f a) - WeakDual.toStrongDual (f b)‖ ≤
      L * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖)
    (hδε : 2 * L * δ ≤ ε) {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    (α : Ordinal) :
    szlenkIterate ε (f '' K) α ⊆ f '' szlenkIterate δ K α := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
      obtain rfl := hα.eq_bot
      simp
  | succ α hα ih =>
      rw [szlenkIterate_succ, szlenkIterate_succ]
      exact (szlenkDeriv_mono ε ih).trans
        (szlenkDeriv_image_subset f hf hL hfL hδε (szlenkIterate_isCompact δ hK α))
  | isSuccLimit α hα ih =>
      intro x hx
      letI : Nonempty (Set.Iio α) := ⟨⟨0, hα.bot_lt⟩⟩
      let A : Set.Iio α → Set (WeakDual 𝕜 E) :=
        fun β => szlenkIterate δ K β.val ∩ f ⁻¹' {x}
      have hAn : ∀ β, (A β).Nonempty := by
        intro β
        have hxβ : x ∈ szlenkIterate ε (f '' K) β.val :=
          szlenkIterate_antitone ε (f '' K) β.property.le hx
        obtain ⟨y, hy, hfy⟩ := ih β.val β.property hxβ
        exact ⟨y, hy, hfy⟩
      have hAc : ∀ β, IsCompact (A β) := fun β =>
        (szlenkIterate_isCompact δ hK β.val).inter_right (isClosed_singleton.preimage hf)
      have hAcl : ∀ β, IsClosed (A β) := fun β => (hAc β).isClosed
      have hAd : Directed (· ⊇ ·) A := by
        intro β γ
        refine ⟨max β γ, ?_, ?_⟩
        · exact inter_subset_inter_left _ (szlenkIterate_antitone δ K (le_max_left β γ))
        · exact inter_subset_inter_left _ (szlenkIterate_antitone δ K (le_max_right β γ))
      obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        A hAd hAn hAc hAcl
      refine ⟨y, ?_, (mem_iInter.mp hy ⟨0, hα.bot_lt⟩).2⟩
      rw [szlenkIterate_limit δ K α hα]
      exact mem_iInter.mpr (fun β => (mem_iInter.mp hy β).1)

theorem HasSzlenkBound.image
    {K : Set (WeakDual 𝕜 E)} {α : Ordinal} (h : HasSzlenkBound K α)
    (hK : IsCompact K) (f : WeakDual 𝕜 E → WeakDual 𝕜 F) (hf : Continuous f)
    {L : ℝ} (hL : 0 < L)
    (hfL : ∀ a b, ‖WeakDual.toStrongDual (f a) - WeakDual.toStrongDual (f b)‖ ≤
      L * ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖) :
    HasSzlenkBound (f '' K) α := by
  intro ε hε
  have hδ : 0 < ε / (2 * L) := div_pos hε (by positivity)
  have hδε : 2 * L * (ε / (2 * L)) ≤ ε := by
    rw [mul_div_cancel₀ ε (ne_of_gt (by positivity : 0 < 2 * L))]
  have hi := szlenkIterate_image_subset f hf hL.le hfL hδε hK α
  rw [h _ hδ, Set.image_empty] at hi
  exact Set.eq_empty_of_subset_empty hi

end Posets
