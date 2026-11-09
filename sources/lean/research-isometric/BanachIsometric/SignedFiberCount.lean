import BanachIsometric.BranchFiberSum

/-!
# Integer orientation counts on finite actual fibers

The total count is defined from the actual fiber, with value zero on infinite
fibers. This is an analytic signed count, not yet asserted to be Brouwer degree.
-/

namespace BanachIsometric

open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def signedFiberCount (f : E → E) (D : E → E →L[ℝ] E)
    (s : Set E) (y : E) : ℤ := by
  classical
  exact if hfin : {x : E | x ∈ s ∧ f x = y}.Finite then finiteSignedFiberCount f D s y hfin else 0

theorem signedFiberSum_eq_coe_signedFiberCount
    (f : E → E) (D : E → E →L[ℝ] E) (s : Set E) (y : E)
    (hfin : {x : E | x ∈ s ∧ f x = y}.Finite) :
    signedFiberSum f D s y = (signedFiberCount f D s y : ℝ) := by
  rw [signedFiberCount, dif_pos hfin]
  exact signedFiberSum_eq_finiteSignedFiberCount f D s y hfin

/-- Only membership in the source along the specified actual fiber affects
the fiber sum. -/
theorem signedFiberSum_congr_source_on_fiber
    (f : E → E) (D : E → E →L[ℝ] E) {s t : Set E} (y : E)
    (h : ∀ x, f x = y → (x ∈ s ↔ x ∈ t)) :
    signedFiberSum f D s y = signedFiberSum f D t y := by
  classical
  let e : {x : E // x ∈ s ∧ f x = y} ≃ {x : E // x ∈ t ∧ f x = y} :=
    Equiv.subtypeEquivRight (fun x => by
      constructor
      · intro hx
        exact ⟨(h x hx.2).mp hx.1, hx.2⟩
      · intro hx
        exact ⟨(h x hx.2).mpr hx.1, hx.2⟩)
  exact e.tsum_eq (fun x => jacobianOrientation D x.val)

theorem signedFiberSum_inter_eq_of_fiber_subset
    (f : E → E) (D : E → E →L[ℝ] E) (s R : Set E) (y : E)
    (h : ∀ x ∈ s, f x = y → x ∈ R) :
    signedFiberSum f D (s ∩ R) y = signedFiberSum f D s y := by
  apply signedFiberSum_congr_source_on_fiber f D y
  intro x hxy
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, h x hx hxy⟩⟩

end BanachIsometric
