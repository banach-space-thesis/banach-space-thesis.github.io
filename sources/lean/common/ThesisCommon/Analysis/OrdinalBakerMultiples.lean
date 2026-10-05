import ThesisCommon.Analysis.OrdinalBakerNormal
import ThesisCommon.Analysis.OrdinalCharacteristic
import Mathlib.SetTheory.Ordinal.Exponential

/-! The successor and limit arithmetic behind the Cantor--Bendixson
derivatives of ordinal intervals. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

def ordinalPositiveMultiples (κ : Ordinal.{u}) : Set Ordinal.{u} :=
  {x | x ≠ 0 ∧ κ ∣ x}

theorem ordinal_range_mul (κ : Ordinal.{u}) :
    range (κ * ·) = {0} ∪ ordinalPositiveMultiples κ := by
  ext x
  change (∃ y, κ * y = x) ↔ x = 0 ∨ (x ≠ 0 ∧ κ ∣ x)
  constructor
  · rintro ⟨y, rfl⟩
    by_cases h : κ * y = 0
    · exact Or.inl h
    · exact Or.inr ⟨h, dvd_mul_right _ _⟩
  · rintro (rfl | ⟨_, y, hy⟩)
    · exact ⟨0, mul_zero κ⟩
    · exact ⟨y, hy.symm⟩

theorem ordinal_derivedSet_range_mul {κ : Ordinal.{u}} (hκ : 0 < κ) :
    derivedSet (range (κ * ·)) = ordinalPositiveMultiples (κ * Ordinal.omega0) := by
  rw [← image_univ, derivedSet_image_closedEmbedding
    (ordinal_normal_isClosedEmbedding (Ordinal.isNormal_mul_right hκ)), ordinal_derivedSet_univ]
  ext x
  constructor
  · rintro ⟨y, ⟨hy0, z, hz⟩, rfl⟩
    refine ⟨mul_ne_zero hκ.ne' hy0, z, ?_⟩
    rw [hz, mul_assoc]
  · rintro ⟨hx, z, rfl⟩
    refine ⟨Ordinal.omega0 * z, ⟨?_, dvd_mul_right _ _⟩, ?_⟩
    · intro hz
      apply hx
      rw [mul_assoc, hz, mul_zero]
    · rw [mul_assoc]

theorem ordinal_derivedSet_positiveMultiples {κ : Ordinal.{u}} (hκ : 0 < κ) :
    derivedSet (ordinalPositiveMultiples κ) =
      ordinalPositiveMultiples (κ * Ordinal.omega0) := by
  have h := ordinal_derivedSet_range_mul hκ
  rw [ordinal_range_mul, derivedSet_union,
    derivedSet_eq_empty_of_finite (finite_singleton 0), empty_union] at h
  exact h

theorem ordinal_opow_dvd_limit_iff {α x : Ordinal.{u}} (hα : IsSuccLimit α) :
    Ordinal.omega0 ^ α ∣ x ↔ ∀ β < α, Ordinal.omega0 ^ β ∣ x := by
  constructor
  · intro h β hβ
    exact (Ordinal.opow_dvd_opow _ hβ.le).trans h
  · intro h
    apply Ordinal.dvd_of_mod_eq_zero
    by_contra hr
    have hrlt := Ordinal.mod_lt x (Ordinal.opow_ne_zero α Ordinal.omega0_ne_zero)
    obtain ⟨β, hβ, hb⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hα).mp hrlt
    have hd : Ordinal.omega0 ^ β ∣ x % (Ordinal.omega0 ^ α) := by
      apply Ordinal.dvd_iff_mod_eq_zero.mpr
      rw [Ordinal.mod_mod_of_dvd x (Ordinal.opow_dvd_opow _ hβ.le)]
      exact Ordinal.mod_eq_zero_of_dvd (h β hβ)
    have he := Ordinal.mod_eq_zero_of_dvd hd
    rw [Ordinal.mod_eq_of_lt hb] at he
    exact hr he

end ThesisCommon
