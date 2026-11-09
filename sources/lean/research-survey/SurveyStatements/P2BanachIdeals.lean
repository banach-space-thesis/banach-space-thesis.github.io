import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Order.Zorn

/-! Closure and properness of two-sided ideals in a complete normed ring.

This is the analytic step used in the source's maximal-ideal construction.
It does not assert that a maximal proper ideal has already been chosen.
-/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2
variable {R : Type*} [NormedRing R]

/-- The union of a nonempty chain of two-sided ideals is a two-sided ideal. -/
def chainUnionIdeal (c : Set (TwoSidedIdeal R)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {x | ∃ I ∈ c, x ∈ I}
    (by obtain ⟨I, hI⟩ := hne; exact ⟨I, hI, I.zero_mem⟩)
    (by
      intro x y hx hy
      obtain ⟨I, hI, hx⟩ := hx
      obtain ⟨J, hJ, hy⟩ := hy
      rcases hc.total hI hJ with hIJ | hJI
      · exact ⟨J, hJ, J.add_mem (hIJ hx) hy⟩
      · exact ⟨I, hI, I.add_mem hx (hJI hy)⟩)
    (by
      intro x hx
      obtain ⟨I, hI, hx⟩ := hx
      exact ⟨I, hI, I.neg_mem hx⟩)
    (by
      intro x y hy
      obtain ⟨I, hI, hy⟩ := hy
      exact ⟨I, hI, I.mul_mem_left x y hy⟩)
    (by
      intro x y hx
      obtain ⟨I, hI, hx⟩ := hx
      exact ⟨I, hI, I.mul_mem_right x y hx⟩)

/-- Zorn's lemma supplies an algebraically maximal proper two-sided ideal. -/
theorem exists_isCoatom_twoSidedIdeal [Nontrivial R] :
    ∃ J : TwoSidedIdeal R, IsCoatom J := by
  obtain ⟨J, _, hmax⟩ := zorn_le_nonempty₀ {I : TwoSidedIdeal R | I ≠ ⊤}
    (fun c hc hchain I hI => by
      let U := chainUnionIdeal c hchain ⟨I, hI⟩
      have hU : U ≠ ⊤ := by
        intro htop
        have hone := U.one_mem htop
        have hone' : ∃ J ∈ c, (1 : R) ∈ J := by
          simpa only [U, chainUnionIdeal, TwoSidedIdeal.mem_mk'] using hone
        obtain ⟨J, hJ, h1⟩ := hone'
        exact hc hJ (J.eq_top h1)
      refine ⟨U, hU, ?_⟩
      intro J hJ x hx
      simpa only [U, chainUnionIdeal, TwoSidedIdeal.mem_mk'] using
        (show ∃ K ∈ c, x ∈ K from ⟨J, hJ, hx⟩))
    (⊥ : TwoSidedIdeal R) bot_ne_top
  exact ⟨J, isCoatom_iff_ge_of_le.mpr hmax⟩

/-- The norm closure is still a two-sided ideal. -/
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

/-- A proper two-sided ideal remains proper on taking its norm closure. -/
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
  simpa only [Ideal.coe_closure, TwoSidedIdeal.coe_asIdeal,
    ← coe_twoSidedIdealClosure] using hone

/-- Every algebraically maximal proper two-sided ideal is norm closed. -/
theorem isClosed_of_isCoatom_twoSidedIdeal (J : TwoSidedIdeal R)
    (hJ : IsCoatom J) : IsClosed (J : Set R) := by
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

/-- The source's maximal-ideal existence lemma, with no ideal hypothesis added. -/
theorem exists_closed_isCoatom_twoSidedIdeal [Nontrivial R] :
    ∃ J : TwoSidedIdeal R, IsCoatom J ∧ IsClosed (J : Set R) := by
  obtain ⟨J, hJ⟩ := exists_isCoatom_twoSidedIdeal (R := R)
  exact ⟨J, hJ, isClosed_of_isCoatom_twoSidedIdeal J hJ⟩

end SurveyStatements.P2
