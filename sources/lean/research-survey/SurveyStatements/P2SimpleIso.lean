import SurveyStatements.P2Calkin
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-! The genuine Banach-algebra isomorphism transports algebraic simplicity. -/

noncomputable section
set_option autoImplicit false

namespace SurveyStatements.P2
universe u v
variable (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

theorem CalkinBanachAlgebraIso.simple_of_simple (e : CalkinBanachAlgebraIso X A)
    (hA : ∀ I : TwoSidedIdeal A, I = ⊥ ∨ I = ⊤)
    (J : TwoSidedIdeal (Calkin X)) : J = ⊥ ∨ J = ⊤ := by
  let r := CalkinBanachAlgebraIso.toAlgEquiv X e
  let q := r.symm.toRingHom
  rcases hA (J.comap q) with h | h
  · left
    apply SetLike.ext
    intro x
    rw [TwoSidedIdeal.mem_bot]
    constructor
    · intro hx
      have hmem : r x ∈ J.comap q := (TwoSidedIdeal.mem_comap q).mpr (by
        change r.symm (r x) ∈ J
        simpa only [AlgEquiv.symm_apply_apply] using hx)
      rw [h, TwoSidedIdeal.mem_bot] at hmem
      exact r.injective (hmem.trans r.map_zero.symm)
    · intro hx
      rw [hx]
      exact J.zero_mem
  · right
    apply SetLike.ext
    intro x
    constructor
    · intro _
      exact TwoSidedIdeal.mem_top _
    · intro _
      have hmem : r x ∈ J.comap q := by rw [h]; exact TwoSidedIdeal.mem_top _
      have hx := (TwoSidedIdeal.mem_comap q).mp hmem
      change r.symm (r x) ∈ J at hx
      simpa only [AlgEquiv.symm_apply_apply] using hx

end SurveyStatements.P2
