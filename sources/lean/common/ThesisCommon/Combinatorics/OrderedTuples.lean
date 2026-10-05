import ThesisCommon.Combinatorics.OrderedFiniteRamsey
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Concrete ordered pairs, triples, quadruples and finite windows. -/
noncomputable section
namespace ThesisCommon

def orderedPair (a b : ℕ) (hab : a < b) : Fin 2 ↪o ℕ :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)

def orderedTriple (a b c : ℕ) (hab : a < b) (hbc : b < c) : Fin 3 ↪o ℕ :=
  OrderEmbedding.ofStrictMono ![a, b, c] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    omega)

def orderedQuadruple (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d) : Fin 4 ↪o ℕ :=
  OrderEmbedding.ofStrictMono ![a, b, c, d] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals omega)

theorem range_orderedPair_subset {S : Set ℕ} {a b : ℕ} (hab : a < b)
    (ha : a ∈ S) (hb : b ∈ S) : Set.range (orderedPair a b hab) ⊆ S := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem range_orderedTriple_subset {S : Set ℕ} {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : Set.range (orderedTriple a b c hab hbc) ⊆ S := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

theorem range_orderedQuadruple_subset {S : Set ℕ} {a b c d : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    Set.range (orderedQuadruple a b c d hab hbc hcd) ⊆ S := by
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

def orderedWindow {L m : ℕ} (e : Fin L ↪o ℕ) (offset : ℕ) (h : offset + m ≤ L) :
    Fin m ↪o ℕ := OrderEmbedding.ofStrictMono
  (fun i => e ⟨offset + i.val, by omega⟩) (by
    intro i j hij
    apply e.strictMono
    change offset + i.val < offset + j.val
    exact Nat.add_lt_add_left hij offset)

@[simp] theorem orderedWindow_apply {L m : ℕ} (e : Fin L ↪o ℕ) (offset : ℕ)
    (h : offset + m ≤ L) (i : Fin m) : orderedWindow e offset h i = e ⟨offset + i.val, by omega⟩ := rfl

end ThesisCommon
