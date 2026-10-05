import Mathlib.Order.WellFounded
import Mathlib.Order.Monotone.Basic

/-! Well-founded choice of compatible stages. The extension premise is
explicit; the resulting family is constructed by well-founded recursion. -/
noncomputable section
open scoped Classical
namespace ThesisCommon
variable {I P : Type*} [LinearOrder I] [WellFoundedLT I] [PartialOrder P]
variable (p₀ : P) (Good : I → P → Prop)

def CoherentPast (i : I) (f : ∀ j, j < i → P) : Prop :=
  ∀ j hj, Good j (f j hj) ∧ ∀ k hk, k < j → f k hk ≤ f j hj

variable (step : ∀ i (f : ∀ j, j < i → P), CoherentPast Good i f →
  ∃ p, Good i p ∧ ∀ j hj, f j hj ≤ p)

private def coherentSelect (i : I) (f : ∀ j, j < i → P) : P :=
  if h : CoherentPast Good i f then (step i f h).choose else p₀

def wellOrderCoherentConstruction : I → P :=
  (wellFounded_lt : WellFounded ((· < ·) : I → I → Prop)).fix
    (coherentSelect p₀ Good step)

theorem wellOrderCoherentConstruction_spec (i : I) :
    Good i (wellOrderCoherentConstruction p₀ Good step i) ∧
      ∀ j, j < i → wellOrderCoherentConstruction p₀ Good step j ≤
        wellOrderCoherentConstruction p₀ Good step i := by
  induction i using (wellFounded_lt : WellFounded ((· < ·) : I → I → Prop)).induction with
  | h i ih =>
    let f : ∀ j, j < i → P := fun j _ => wellOrderCoherentConstruction p₀ Good step j
    have hf : CoherentPast Good i f := by
      intro j hj
      refine ⟨(ih j hj).1, ?_⟩
      intro k hk hkj
      exact (ih j hj).2 k hkj
    have heq : wellOrderCoherentConstruction p₀ Good step i = (step i f hf).choose := by
      conv_lhs => rw [wellOrderCoherentConstruction, WellFounded.fix_eq]
      change coherentSelect p₀ Good step i f = _
      rw [coherentSelect, dif_pos hf]
    rw [heq]
    exact (step i f hf).choose_spec

theorem wellOrderCoherentConstruction_monotone :
    Monotone (wellOrderCoherentConstruction p₀ Good step) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact (wellOrderCoherentConstruction_spec p₀ Good step j).2 i hij

include p₀ step in
theorem exists_coherent_wellOrder_family :
    ∃ f : I → P, Monotone f ∧ ∀ i, Good i (f i) :=
  ⟨wellOrderCoherentConstruction p₀ Good step,
    wellOrderCoherentConstruction_monotone p₀ Good step,
    fun i => (wellOrderCoherentConstruction_spec p₀ Good step i).1⟩

end ThesisCommon
