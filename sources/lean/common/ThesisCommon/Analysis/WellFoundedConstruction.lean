import Mathlib.Order.WellFounded

/-! Dependent well-founded choice with an invariant on the entire earlier history. -/
noncomputable section
namespace ThesisCommon

def historyThrough {I : Type*} [LinearOrder I] {D : I → Type*}
    (fallback : ∀ i, D i) (a : I) (f : ∀ j, j < a → D j) (x : D a) : ∀ i, D i :=
  Function.update (fun j => if h : j < a then f j h else fallback j) a x

theorem historyThrough_self {I : Type*} [LinearOrder I] {D : I → Type*}
    (fallback : ∀ i, D i) (a : I) (f : ∀ j, j < a → D j) (x : D a) :
    historyThrough fallback a f x a = x := Function.update_self _ _ _

theorem historyThrough_lt {I : Type*} [LinearOrder I] {D : I → Type*}
    (fallback : ∀ i, D i) (a : I) (f : ∀ j, j < a → D j) (x : D a)
    {i : I} (hi : i < a) : historyThrough fallback a f x i = f i hi := by
  unfold historyThrough
  rw [Function.update_of_ne (ne_of_lt hi), dif_pos hi]

theorem wellFounded_history_choice {I : Type*} {r : I → I → Prop}
    (hwf : WellFounded r) (htrans : Transitive r)
    (D : I → Type*) (hne : ∀ i, Nonempty (D i))
    (P : ∀ i, (∀ j, r j i → D j) → D i → Prop)
    (step : ∀ i (f : ∀ j, r j i → D j),
      (∀ j (hji : r j i), P j (fun k hkj => f k (htrans hkj hji)) (f j hji)) →
      ∃ d, P i f d) :
    ∃ f : ∀ i, D i, ∀ i, P i (fun j _ => f j) (f i) := by
  classical
  let next : ∀ i, (∀ j, r j i → D j) → D i := fun i f =>
    if h : ∀ j (hji : r j i), P j (fun k hkj => f k (htrans hkj hji)) (f j hji)
    then Classical.choose (step i f h)
    else @Classical.arbitrary (D i) (hne i)
  let f : ∀ i, D i := hwf.fix next
  refine ⟨f, ?_⟩
  intro i
  induction i using hwf.induction with
  | h i ih =>
    have hprev : ∀ j (hji : r j i),
        P j (fun k _ => f k) (f j) := fun j hji => ih j hji
    have heq : f i = next i (fun j _ => f j) := hwf.fix_eq next i
    rw [heq]
    dsimp only [next]
    rw [dif_pos hprev]
    exact Classical.choose_spec (step i (fun j _ => f j) hprev)

end ThesisCommon
