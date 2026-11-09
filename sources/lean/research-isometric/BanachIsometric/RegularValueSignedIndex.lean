import BanachIsometric.SignedIndexFiniteRootValues
import BanachIsometric.RegularRootSignedIndex
import BanachIsometric.RegularFiberFiniteness
import BanachIsometric.SignedCountPositive

/-!
# The actual regular-value formula for the canonical signed index

Every root in the compact box is assumed differentiable with nonzero actual
derivative determinant. Its isolation and the finiteness of the entire fiber
are derived. Actual disjoint root boxes, compact source excision, finite count
additivity, and actual derivative linearization then prove the formula.
Neither local injectivity nor an index-additivity axiom is assumed.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal BigOperators

noncomputable section

theorem localSignedIndex_eq_signedFiberCount_of_regular_value
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b)
    (hreg : ∀ x ∈ Icc a b, f x = c →
      DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).det ≠ 0) :
    localSignedIndex f a b c = signedFiberCount f (fderiv ℝ f) (Icc a b) c := by
  classical
  have hfin : {x : PiolaSpace n | x ∈ Icc a b ∧ f x = c}.Finite := by
    have h := finite_actual_regular_fiber isCompact_Icc hf.continuous.continuousOn hreg
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using h
  letI : Fintype (ActualBoxFiber f a b c) := hfin.fintype
  have hlocal (x : ActualBoxFiber f a b c) : ∃ r > 0, ∀ s : ℝ, 0 < s → s ≤ r →
      localSignedIndex f (x.val - s • (1 : PiolaSpace n)) (x.val + s • 1) c =
        (SignType.sign (fderiv ℝ f x.val).det : ℤ) := by
    obtain ⟨r, hr, hsmall⟩ := exists_regular_root_cube_signed_index hf
      (hreg x.val x.property.1 x.property.2).1.hasFDerivAt
      (hreg x.val x.property.1 x.property.2).2
    refine ⟨r, hr, fun s hs hsr => ?_⟩
    have h := hsmall s hs hsr
    rwa [x.property.2] at h
  have h := localSignedIndex_eq_sum_of_local_root_values hf a b c hab hc
    (fun x => (SignType.sign (fderiv ℝ f x.val).det : ℤ)) hlocal
  rw [signedFiberCount, dif_pos hfin]
  change localSignedIndex f a b c =
    ∑ x : ActualBoxFiber f a b c, (SignType.sign (fderiv ℝ f x.val).det : ℤ)
  exact h

theorem localSignedIndex_eq_natCard_of_positive_regular_value
    {n : ℕ} [NeZero n] {f : PiolaSpace n → PiolaSpace n} {C : ℝ≥0}
    (hf : LipschitzWith C f) (a b : PiolaSpace n) (hab : a ≤ b) (c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b)
    (hdiff : ∀ x ∈ Icc a b, f x = c → DifferentiableAt ℝ f x)
    (hpos : ∀ x ∈ Icc a b, f x = c → 0 < (fderiv ℝ f x).det) :
    localSignedIndex f a b c = (Nat.card (ActualBoxFiber f a b c) : ℤ) := by
  have hreg (x) (hx : x ∈ Icc a b) (hxc : f x = c) :=
    And.intro (hdiff x hx hxc) (hpos x hx hxc).ne'
  have hfin : {x : PiolaSpace n | x ∈ Icc a b ∧ f x = c}.Finite := by
    have h := finite_actual_regular_fiber isCompact_Icc hf.continuous.continuousOn hreg
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_singleton_iff] using h
  rw [localSignedIndex_eq_signedFiberCount_of_regular_value hf a b hab c hc hreg]
  exact signedFiberCount_eq_card_of_pos_det f (fderiv ℝ f) (Icc a b) c hfin hpos

end

end BanachIsometric
