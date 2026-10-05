import ThesisCommon.Analysis.BandProjectionPositive
import Mathlib.Order.Bounds.OrderIso

/-! Transport of solid order-closed submodules through actual compatible
linear and order isomorphisms. No ideal or band preservation is assumed. -/
noncomputable section
open Set
namespace ThesisCommon
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [ConditionallyCompleteLattice F] [IsOrderedAddMonoid F]

omit [IsOrderedAddMonoid E] [IsOrderedAddMonoid F] in
theorem IsOrderClosedIdeal.comap_linearOrderIso {J : Submodule ℝ F}
    (hJ : IsOrderClosedIdeal J) (e : E ≃ₗ[ℝ] F) (o : E ≃o F)
    (heo : ∀ x, e x = o x) : IsOrderClosedIdeal (J.comap e.toLinearMap) := by
  have hzero : o 0 = 0 := by rw [← heo, map_zero]
  have habs (x : E) : e |x| = |e x| := by
    change e (x ⊔ -x) = e x ⊔ -e x
    rw [heo, o.map_sup, ← heo, ← heo, map_neg]
  constructor
  · intro x y hy hxy
    change e x ∈ J
    apply hJ.solid hy
    change |e x| ≤ |e y|
    rw [← habs, ← habs, heo, heo]
    exact o.monotone hxy
  · intro s hs hmem hpos hdir x hx
    change e x ∈ J
    rw [heo]
    apply hJ.closed (hs.image o)
    · rintro _ ⟨y, hy, rfl⟩
      rw [← heo]
      exact hmem y hy
    · rintro _ ⟨y, hy, rfl⟩
      simpa only [hzero] using o.monotone (hpos y hy)
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hyw, hzw⟩ := hdir y hy z hz
      exact ⟨o w, ⟨w, hw, rfl⟩, o.monotone hyw, o.monotone hzw⟩
    · exact o.isLUB_image'.mpr hx

end ThesisCommon
