import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The increasing submultiplicative hull used by Gowers--Maurey.
Its value is the infimum of actual finite factorization costs, with
factors at least one and product at least the argument. -/
noncomputable section
namespace ThesisCommon

def factorizationCosts (φ : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {a | ∃ l : List ℝ, (∀ t ∈ l, 1 ≤ t) ∧ x ≤ l.prod ∧ a = (l.map φ).prod}

def submultiplicativeHull (φ : ℝ → ℝ) (x : ℝ) : ℝ := sInf (factorizationCosts φ x)

theorem list_prod_ge_one {l : List ℝ} (h : ∀ t ∈ l, 1 ≤ t) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.prod_cons]
    have ht := h t (List.mem_cons_self ..)
    have hl := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    nlinarith

theorem factorizationCosts_nonempty (φ : ℝ → ℝ) (x : ℝ) :
    (factorizationCosts φ x).Nonempty := by
  refine ⟨φ (max 1 x), [max 1 x], ?_, ?_, ?_⟩ <;> simp

theorem factorizationCosts_ge_one {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    {x a : ℝ} (ha : a ∈ factorizationCosts φ x) : 1 ≤ a := by
  obtain ⟨l, hl, _, rfl⟩ := ha
  apply list_prod_ge_one
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  exact hφ t (hl t ht)

theorem factorizationCosts_bddBelow {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (x : ℝ) :
    BddBelow (factorizationCosts φ x) := ⟨1, fun _ ha => factorizationCosts_ge_one hφ ha⟩

theorem one_le_submultiplicativeHull {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (x : ℝ) :
    1 ≤ submultiplicativeHull φ x :=
  le_csInf (factorizationCosts_nonempty φ x) (fun _ ha => factorizationCosts_ge_one hφ ha)

theorem submultiplicativeHull_le {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    {x : ℝ} (hx : 1 ≤ x) : submultiplicativeHull φ x ≤ φ x := by
  apply csInf_le (factorizationCosts_bddBelow hφ x)
  exact ⟨[x], by simpa using hx, by simp, by simp⟩

theorem submultiplicativeHull_mono {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) :
    Monotone (submultiplicativeHull φ) := by
  intro x y hxy
  apply le_csInf (factorizationCosts_nonempty φ y)
  rintro a ⟨l, hl, hy, rfl⟩
  exact csInf_le (factorizationCosts_bddBelow hφ x) ⟨l, hl, hxy.trans hy, rfl⟩

theorem factorizationCosts_mul {φ : ℝ → ℝ} {x y a b : ℝ}
    (hy : 1 ≤ y)
    (ha : a ∈ factorizationCosts φ x) (hb : b ∈ factorizationCosts φ y) :
    a * b ∈ factorizationCosts φ (x * y) := by
  obtain ⟨l, hl, hxl, rfl⟩ := ha
  obtain ⟨m, hm, hym, rfl⟩ := hb
  refine ⟨l ++ m, ?_, ?_, ?_⟩
  · intro t ht
    exact (List.mem_append.mp ht).elim (hl t) (hm t)
  · rw [List.prod_append]
    exact mul_le_mul hxl hym (zero_le_one.trans hy) (zero_le_one.trans (list_prod_ge_one hl))
  · simp

theorem submultiplicativeHull_mul_le {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    {x y : ℝ} (_hx : 1 ≤ x) (hy : 1 ≤ y) :
    submultiplicativeHull φ (x * y) ≤ submultiplicativeHull φ x * submultiplicativeHull φ y := by
  have hpair : ∀ a ∈ factorizationCosts φ x, ∀ b ∈ factorizationCosts φ y,
      submultiplicativeHull φ (x * y) ≤ a * b := by
    intro a ha b hb
    exact csInf_le (factorizationCosts_bddBelow hφ _) (factorizationCosts_mul hy ha hb)
  have ha : ∀ a ∈ factorizationCosts φ x,
      submultiplicativeHull φ (x * y) ≤ a * submultiplicativeHull φ y := by
    intro a ha
    have ha0 : 0 < a := zero_lt_one.trans_le (factorizationCosts_ge_one hφ ha)
    rw [mul_comm a, ← div_le_iff₀ ha0]
    apply le_csInf (factorizationCosts_nonempty φ y)
    intro b hb
    exact (div_le_iff₀ ha0).mpr (by simpa only [mul_comm] using hpair a ha b hb)
  have hy0 : 0 < submultiplicativeHull φ y := zero_lt_one.trans_le (one_le_submultiplicativeHull hφ y)
  apply (div_le_iff₀ hy0).mp
  apply le_csInf (factorizationCosts_nonempty φ x)
  intro a ha'
  exact (div_le_iff₀ hy0).mpr (ha a ha')

theorem le_submultiplicativeHull {φ ψ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hψ : ∀ x, 1 ≤ x → 0 ≤ ψ x)
    (hψone : ψ 1 ≤ 1) (hmono : MonotoneOn ψ (Set.Ici 1))
    (hmul : ∀ x y, 1 ≤ x → 1 ≤ y → ψ (x * y) ≤ ψ x * ψ y)
    (hle : ∀ x, 1 ≤ x → ψ x ≤ φ x) {x : ℝ} (hx : 1 ≤ x) :
    ψ x ≤ submultiplicativeHull φ x := by
  have hprod : ∀ l : List ℝ, (∀ t ∈ l, 1 ≤ t) → ψ l.prod ≤ (l.map φ).prod := by
    intro l
    induction l with
    | nil => simpa using hψone
    | cons t l ih =>
      intro hl
      have ht := hl t (List.mem_cons_self ..)
      have htail : ∀ s ∈ l, 1 ≤ s := fun s hs => hl s (List.mem_cons_of_mem _ hs)
      have hp := list_prod_ge_one htail
      simp only [List.prod_cons, List.map_cons]
      exact (hmul t l.prod ht hp).trans (mul_le_mul (hle t ht) (ih htail)
        (hψ l.prod hp) (zero_le_one.trans (hφ t ht)))
  apply le_csInf (factorizationCosts_nonempty φ x)
  rintro a ⟨l, hl, hxl, rfl⟩
  exact (hmono hx (list_prod_ge_one hl) hxl).trans (hprod l hl)

end ThesisCommon
