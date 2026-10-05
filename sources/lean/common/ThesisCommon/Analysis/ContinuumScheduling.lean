import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.NormNum

/-! Countable histories and repeated scheduling at the continuum ordinal.
No regularity of the continuum, or continuum hypothesis, is used. -/
noncomputable section
open Set Cardinal
namespace ThesisCommon

theorem aleph0_lt_cof_continuum : ℵ₀ < (𝔠 : Cardinal.{0}).ord.cof := by
  rw [← Cardinal.two_power_aleph0]
  exact Cardinal.lt_cof_power le_rfl (by norm_num)

theorem countable_below_continuum_stage
    {S : Set (𝔠 : Cardinal.{0}).ord.toType} (hS : S.Countable) :
    ∃ a, ∀ b ∈ S, b < a := by
  apply Ordinal.lt_cof_type (r := (· < ·))
  rw [Ordinal.type_toType]
  exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt aleph0_lt_cof_continuum

/-- Every code is repeated cofinally often in a continuum-sized well order
whose proper initial segments have cardinality less than the continuum. -/
theorem exists_cofinal_schedule {I Code : Type} [LinearOrder I] [Nonempty Code]
    (hI : #I = 𝔠) (hsmall : ∀ a : I, #(Set.Iio a) < 𝔠) (hCode : #Code ≤ 𝔠) :
    ∃ schedule : I → Code, ∀ c a, ∃ b, a ≤ b ∧ schedule b = c := by
  classical
  have hprod : #(Code × I) = 𝔠 := by
    apply le_antisymm
    · rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, hI]
      exact (mul_le_mul_right' hCode 𝔠).trans_eq Cardinal.continuum_mul_self
    · rw [← hI]
      exact Cardinal.mk_le_of_injective (f := fun i : I => (Classical.choice ‹Nonempty Code›, i))
        (fun _ _ h => congrArg Prod.snd h)
  obtain ⟨e⟩ := Cardinal.eq.mp (hI.trans hprod.symm)
  refine ⟨fun i => (e i).1, ?_⟩
  intro c a
  by_contra h
  have hlt (j : I) : e.symm (c,j) < a := by
    apply lt_of_not_ge
    intro hle
    apply h
    exact ⟨e.symm (c,j),hle,by simp⟩
  let f : I → Set.Iio a := fun j => ⟨e.symm (c,j), hlt j⟩
  have hf : Function.Injective f := by
    intro j k h
    have he := e.symm.injective (congrArg Subtype.val h)
    exact congrArg Prod.snd he
  exact (hsmall a).not_ge (hI ▸ Cardinal.mk_le_of_injective hf)

end ThesisCommon
