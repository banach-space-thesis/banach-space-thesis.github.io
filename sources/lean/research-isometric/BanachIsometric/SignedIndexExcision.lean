import BanachIsometric.LocalSignedIndex
import BanachIsometric.SignedCountExcision

/-! # Excision and source-box independence of the canonical actual signed index -/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped NNReal

variable {n : ℕ}

theorem IsLocalSignedIndex.congr_source
    {f : PiolaSpace n → PiolaSpace n} {a b a' b' c : PiolaSpace n} {D : ℤ}
    (hD : IsLocalSignedIndex f a b c D) {r : ℝ} (hr : 0 < r)
    (hsource : ∀ y ∈ ball c r, ∀ x, f x = y →
      (x ∈ Icc a b ↔ x ∈ Icc a' b')) : IsLocalSignedIndex f a' b' c D := by
  obtain ⟨s, hs, hDs⟩ := hD
  refine ⟨min r s, lt_min hr hs, ?_⟩
  filter_upwards [hDs] with y hy
  intro hymem
  rw [← signedFiberCount_congr_source_on_fiber f (fderiv ℝ f) y
    (hsource y (ball_subset_ball (min_le_left r s) hymem))]
  exact hy (ball_subset_ball (min_le_right r s) hymem)

theorem localSignedIndex_eq_of_source_congr [NeZero n]
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b a' b' : PiolaSpace n) (hab : a ≤ b) (hab' : a' ≤ b') (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b) (hc' : c ∉ f '' piolaBoxBoundary a' b')
    {r : ℝ} (hr : 0 < r)
    (hsource : ∀ y ∈ ball c r, ∀ x, f x = y →
      (x ∈ Icc a b ↔ x ∈ Icc a' b')) :
    localSignedIndex f a b c = localSignedIndex f a' b' c := by
  exact ((localSignedIndex_spec hf a b hab c hc).congr_source hr hsource).unique
    (localSignedIndex_spec hf a' b' hab' c hc')

end BanachIsometric
