import BanachIsometric.SignedCountAdditivity
import BanachIsometric.LocalSignedIndex

/-!
# Actual local-index additivity for a source-box decomposition

The actual signed counts add almost everywhere by a proved fiber
decomposition. Their canonical local values therefore add on a common target
neighborhood. No additivity property of a proposed degree is assumed.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

theorem localSignedIndex_add_of_box_union
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f)
    (a b a₁ b₁ a₂ b₂ : PiolaSpace n) (hab : a ≤ b) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hunion : Icc a b = Icc a₁ b₁ ∪ Icc a₂ b₂)
    (hnull : volume (Icc a₁ b₁ ∩ Icc a₂ b₂) = 0)
    (c : PiolaSpace n) (hc : c ∉ f '' piolaBoxBoundary a b)
    (hc₁ : c ∉ f '' piolaBoxBoundary a₁ b₁) (hc₂ : c ∉ f '' piolaBoxBoundary a₂ b₂) :
    localSignedIndex f a b c = localSignedIndex f a₁ b₁ c + localSignedIndex f a₂ b₂ c := by
  obtain ⟨r, hr, h₁⟩ := localSignedIndex_spec hf a₁ b₁ hab₁ c hc₁
  obtain ⟨s, hs, h₂⟩ := localSignedIndex_spec hf a₂ b₂ hab₂ c hc₂
  have hadd := ae_signedFiberCount_union_of_compact volume hf
    (isCompact_Icc (a := a₁) (b := b₁)) (isCompact_Icc (a := a₂) (b := b₂)) hnull
  apply localSignedIndex_eq_of_ae_eq_on_ball hf a b hab c hc (lt_min hr hs)
  filter_upwards [hadd, h₁, h₂] with y hyadd hy₁ hy₂
  intro hymem
  rw [hunion, hyadd, hy₁ (ball_subset_ball (min_le_left r s) hymem),
    hy₂ (ball_subset_ball (min_le_right r s) hymem)]

end BanachIsometric
