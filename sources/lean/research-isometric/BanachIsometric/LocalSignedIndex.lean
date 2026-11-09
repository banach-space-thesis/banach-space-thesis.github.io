import BanachIsometric.SignedCountLocalConstancy

/-!
# The canonical actual local signed index

The index is the unique local almost-everywhere value of the actual integer
fiber count. Existence away from the actual boundary image is already proved
analytically; uniqueness follows from positive measure of a common ball. This
definition makes no assumption of degree or of its invariance properties.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal

variable {n : ℕ} [NeZero n]

def IsLocalSignedIndex (f : PiolaSpace n → PiolaSpace n)
    (a b c : PiolaSpace n) (D : ℤ) : Prop :=
  ∃ r > 0, ∀ᵐ y, y ∈ ball c r → signedFiberCount f (fderiv ℝ f) (Icc a b) y = D

omit [NeZero n] in
theorem IsLocalSignedIndex.unique {f : PiolaSpace n → PiolaSpace n}
    {a b c : PiolaSpace n} {D D' : ℤ}
    (hD : IsLocalSignedIndex f a b c D) (hD' : IsLocalSignedIndex f a b c D') : D = D' := by
  obtain ⟨r, hr, hDr⟩ := hD
  obtain ⟨s, hs, hDs⟩ := hD'
  have hpos : 0 < min r s := lt_min hr hs
  have hnonnull : volume (ball c (min r s)) ≠ 0 :=
    isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hpos)
  obtain ⟨y, hy, hyD⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hnonnull
    (ae_restrict_of_ae (hDr.and hDs))
  exact (hyD.1 (ball_subset_ball (min_le_left r s) hy)).symm.trans
    (hyD.2 (ball_subset_ball (min_le_right r s) hy))

noncomputable def localSignedIndex (f : PiolaSpace n → PiolaSpace n)
    (a b c : PiolaSpace n) : ℤ := by
  classical
  exact if h : ∃ D, IsLocalSignedIndex f a b c D then Classical.choose h else 0

theorem localSignedIndex_spec {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b) :
    IsLocalSignedIndex f a b c (localSignedIndex f a b c) := by
  classical
  have hex : ∃ D, IsLocalSignedIndex f a b c D := by
    obtain ⟨r, hr, D, hD⟩ := exists_signedFiberCount_ae_eq_on_ball hf a b hab c hc
    exact ⟨D, r, hr, hD⟩
  simpa only [localSignedIndex, dif_pos hex] using Classical.choose_spec hex

theorem localSignedIndex_eq_of_ae_eq_on_ball
    {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0} (hf : LipschitzWith C f)
    (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b) {r : ℝ} (hr : 0 < r) {D : ℤ}
    (hD : ∀ᵐ y, y ∈ ball c r → signedFiberCount f (fderiv ℝ f) (Icc a b) y = D) :
    localSignedIndex f a b c = D :=
  (localSignedIndex_spec hf a b hab c hc).unique ⟨r, hr, hD⟩

end BanachIsometric
