import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! Closedness of maximal two-sided ideals in a complete normed ring. -/
noncomputable section
namespace ThesisCommon
variable {R : Type*} [NormedRing R]

def twoSidedIdealClosure (J : TwoSidedIdeal R) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' (closure (J : Set R))
    (subset_closure J.zero_mem)
    J.asIdeal.closure.add_mem J.asIdeal.closure.neg_mem
    (fun {x y} hy => J.asIdeal.closure.mul_mem_left x hy)
    (fun {x y} hx => by
      have hmap : Set.MapsTo (fun a : R => a * y) (J : Set R) (J : Set R) :=
        fun a ha => J.mul_mem_right a y ha
      exact hmap.closure (mulRight_continuous y) hx)

@[simp] theorem coe_twoSidedIdealClosure (J : TwoSidedIdeal R) :
    (twoSidedIdealClosure J : Set R) = closure (J : Set R) := by
  simp [twoSidedIdealClosure]

variable [CompleteSpace R]

theorem twoSidedIdealClosure_ne_top (J : TwoSidedIdeal R) (hJ : J ≠ ⊤) :
    twoSidedIdealClosure J ≠ ⊤ := by
  have ha : J.asIdeal ≠ ⊤ := by
    intro h
    exact hJ (J.eq_top (by change (1 : R) ∈ J.asIdeal; rw [h]; trivial))
  have hc := J.asIdeal.closure_ne_top ha
  intro htop
  apply hc
  apply J.asIdeal.closure.eq_top_iff_one.mpr
  have hone := (twoSidedIdealClosure J).one_mem htop
  change (1 : R) ∈ (J.asIdeal.closure : Set R)
  simpa only [Ideal.coe_closure, TwoSidedIdeal.coe_asIdeal, ← coe_twoSidedIdealClosure] using hone

theorem isClosed_of_isCoatom_twoSidedIdeal (J : TwoSidedIdeal R) (hJ : IsCoatom J) :
    IsClosed (J : Set R) := by
  have hle : J ≤ twoSidedIdealClosure J := by
    intro x hx
    change x ∈ (twoSidedIdealClosure J : Set R)
    rw [coe_twoSidedIdealClosure]
    exact subset_closure hx
  have heq : twoSidedIdealClosure J = J :=
    le_antisymm ((isCoatom_iff_ge_of_le.mp hJ).2 _
      (twoSidedIdealClosure_ne_top J hJ.ne_top) hle) hle
  have hset : closure (J : Set R) = (J : Set R) := by
    simpa only [coe_twoSidedIdealClosure] using
      congrArg (fun I : TwoSidedIdeal R => (I : Set R)) heq
  exact closure_eq_iff_isClosed.mp hset

end ThesisCommon
