import ThesisCommon.Analysis.BandProjection

/-! A genuine band projection preserves all existing nonempty suprema. -/
noncomputable section
open Set
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ConditionallyCompleteLattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]
variable {I : Submodule ℝ E}

theorem IsOrderClosedIdeal.bandProjection_isLUB (hI : IsOrderClosedIdeal I)
    {s : Set E} {x : E} (hs : s.Nonempty) (hx : IsLUB s x) :
    IsLUB (bandProjection hI '' s) (bandProjection hI x) := by
  let P := bandProjection hI
  have hP : Monotone P := positive_operator_monotone hI.bandProjection_nonneg
  have hR : Monotone (fun a : E => a - P a) :=
    positive_operator_monotone
      (show 0 ≤ ContinuousLinearMap.id ℝ E - P from sub_nonneg.mpr hI.bandProjection_le_id)
  refine ⟨?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact hP (hx.1 ha)
  · intro y hy
    obtain ⟨a,ha⟩ := hs
    have hPy : P y ≤ y := by
      have h := hR (hy ⟨a,ha,rfl⟩)
      simp only [P,hI.bandProjection_idempotent,sub_self] at h
      exact sub_nonneg.mp h
    have hxy : x ≤ y + (x-P x) := by
      apply hx.2
      intro b hb
      calc
        b = P b + (b-P b) := by abel
        _ ≤ y + (x-P x) := add_le_add (hy ⟨b,hb,rfl⟩) (hR (hx.1 hb))
    have h := hP hxy
    simp only [P,map_add,map_sub,hI.bandProjection_idempotent,sub_self,add_zero] at h
    exact h.trans hPy

end ThesisCommon
