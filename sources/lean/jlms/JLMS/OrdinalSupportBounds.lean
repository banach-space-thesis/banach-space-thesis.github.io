import JLMS.OrdinalTailConstancy
import JLMS.L1Restriction
import Mathlib.Data.Set.Countable

/-!
# Countable supports are bounded below an endpoint of uncountable cofinality

This is the support-bound argument used in Ogden's matrix proofs. An ℓ¹ row
may have a nonzero endpoint coordinate. Its other nonzero coordinates all lie
below one cutoff. A countable family of rows has one common cutoff.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_bound_countable_ordinals {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) {s : Set Ordinal.{u}}
    (hs : s.Countable) (hlt : ∀ x ∈ s, x < α) :
    ∃ β < α, ∀ x ∈ s, x ≤ β := by
  by_cases hne : s.Nonempty
  · obtain ⟨f, hf⟩ := hs.exists_eq_range hne
    have hfl (n : ℕ) : f n < α := hlt (f n) (hf ▸ Set.mem_range_self n)
    refine ⟨⨆ n, f n, Ordinal.iSup_lt_ord_lift (by simpa using hα) hfl, ?_⟩
    intro x hx
    obtain ⟨n, rfl⟩ := hf ▸ hx
    exact Ordinal.le_iSup f n
  · have hpos : 0 < α := by
      apply pos_iff_ne_zero.mpr
      intro h
      simp [h] at hα
    exact ⟨0, hpos, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

theorem exists_ordinal_ellOne_cutoff {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (a : ellOneOn 𝕜 (OrdinalInterval α)) :
    ∃ β < α, ∀ x : OrdinalInterval α, β < x.val → x.val < α → a x = 0 := by
  let s : Set (OrdinalInterval α) := {x | a x ≠ 0 ∧ x.val < α}
  have hs : s.Countable := (ellOneOn_countable_support a).mono (fun x hx => hx.1)
  obtain ⟨β, hβ, hb⟩ := exists_bound_countable_ordinals hα (hs.image Subtype.val)
    (by rintro x ⟨y, hy, rfl⟩; exact hy.2)
  refine ⟨β, hβ, fun x hx hxα => ?_⟩
  by_contra ha
  exact (not_le_of_gt hx) (hb x.val ⟨x, ⟨ha, hxα⟩, rfl⟩)

theorem exists_common_ordinal_ellOne_cutoff {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (a : ℕ → ellOneOn 𝕜 (OrdinalInterval α)) :
    ∃ β < α, ∀ n (x : OrdinalInterval α), β < x.val → x.val < α → a n x = 0 := by
  have h (n) := exists_ordinal_ellOne_cutoff hα (a n)
  choose b hb hf using h
  refine ⟨⨆ n, b n, Ordinal.iSup_lt_ord_lift (by simpa using hα) hb, ?_⟩
  intro n x hx hxα
  exact hf n x ((Ordinal.le_iSup b n).trans_lt hx) hxα

theorem exists_uniform_ordinal_ellOne_cutoff {α σ : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hσ : σ.card < α.cof)
    (a : ∀ x < σ, ellOneOn 𝕜 (OrdinalInterval α)) :
    ∃ β < α, ∀ x (hx : x < σ) (y : OrdinalInterval α),
      β < y.val → y.val < α → a x hx y = 0 := by
  have h (x : Ordinal.{u}) (hx : x < σ) := exists_ordinal_ellOne_cutoff hα (a x hx)
  choose b hb hf using h
  refine ⟨Ordinal.bsup σ b, Ordinal.bsup_lt_ord hσ hb, ?_⟩
  intro x hx y hy hyα
  exact hf x hx y ((Ordinal.le_bsup b x hx).trans_lt hy) hyα

end JLMS
