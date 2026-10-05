import ThesisCommon.Analysis.BooleanStoneSpace
import Mathlib.Order.PrimeSeparator

/-! Prime-ideal separation makes the compact Boolean point representation
faithful. This includes arbitrary Boolean algebras and the trivial case. -/
noncomputable section
open Set
namespace ThesisCommon
variable {B : Type*} [BooleanAlgebra B]

def booleanStonePointOfPrimeIdeal (J : Order.Ideal B) (hJ : Order.Ideal.IsPrime J) :
    BooleanStonePoint B := by
  classical
  refine ⟨fun a => decide (a ∉ J), ?_, ?_, ?_, ?_⟩
  · simp [J.bot_mem]
  · simp [hJ.toIsProper.top_notMem]
  · intro a b
    by_cases ha : a ∈ J
    · have hab : a ⊓ b ∈ J := J.lower inf_le_left ha
      simp [ha, hab]
    · by_cases hb : b ∈ J
      · have hab : a ⊓ b ∈ J := J.lower inf_le_right hb
        simp [hb, hab]
      · have hab : a ⊓ b ∉ J := fun h => (hJ.mem_or_mem h).elim ha hb
        simp [ha, hb, hab]
  · intro a b
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J <;>
      simp [Order.Ideal.sup_mem_iff, ha, hb]

theorem exists_booleanStonePoint_separating {a b : B} (hab : ¬ a ≤ b) :
    ∃ p : BooleanStonePoint B, booleanStoneHom p a = true ∧ booleanStoneHom p b = false := by
  classical
  have hdis : Disjoint (Order.PFilter.principal a : Set B) (Order.Ideal.principal b : Set B) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact hab (hx.trans hx')
  obtain ⟨J, hJ, hbJ, haJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdis
  have hbn : b ∈ J := hbJ Order.Ideal.mem_principal_self
  have han : a ∉ J := Set.disjoint_left.mp haJ (show a ∈ Order.PFilter.principal a from le_rfl)
  refine ⟨booleanStonePointOfPrimeIdeal J hJ, ?_, ?_⟩
  · change decide (a ∉ J) = true
    simp [han]
  · change decide (b ∉ J) = false
    simp [hbn]

theorem booleanStoneSet_subset_iff (a b : B) : booleanStoneSet a ⊆ booleanStoneSet b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨p, ha, hb⟩ := exists_booleanStonePoint_separating hn
    have h' : booleanStoneHom p b = true := h ha
    rw [hb] at h'
    cases h'
  · intro hab p hp
    have h := OrderHomClass.mono (booleanStoneHom p) hab
    change booleanStoneHom p a = true at hp
    change booleanStoneHom p b = true
    rw [hp] at h
    exact top_unique h

theorem booleanStoneSet_injective : Function.Injective (booleanStoneSet (B := B)) := by
  intro a b h
  exact le_antisymm ((booleanStoneSet_subset_iff a b).mp h.le)
    ((booleanStoneSet_subset_iff b a).mp h.ge)

theorem booleanStoneSet_nonempty_iff (a : B) : (booleanStoneSet a).Nonempty ↔ a ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, ← booleanStoneSet_bot]
  exact not_congr booleanStoneSet_injective.eq_iff

end ThesisCommon
