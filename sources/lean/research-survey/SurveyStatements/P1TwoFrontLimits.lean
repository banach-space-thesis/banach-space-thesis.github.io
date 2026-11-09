import SurveyStatements.P1TwoFrontFusion

/-! Limits of the two-front recursion: future points remain in the current
tail, and the combined limit is infinite. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped Classical

namespace SurveyStatements.P1

def finiteFrontLimit (f : ℕ → Finset ℕ) : Set ℕ := ⋃ n : ℕ, (f n : Set ℕ)

theorem finiteFront_subset_limit (f : ℕ → Finset ℕ) (n : ℕ) :
    (f n : Set ℕ) ⊆ finiteFrontLimit f :=
  Set.subset_iUnion (fun n => (f n : Set ℕ)) n

theorem monotone_finiteFront_limit_finite (f : ℕ → Finset ℕ)
    (hf : Monotone f) (hfin : (finiteFrontLimit f).Finite) :
    ∃ N : ℕ, ∀ n : ℕ, f n ⊆ f N := by
  classical
  let index : ℕ → ℕ := fun i => if hi : i ∈ finiteFrontLimit f then
    (Set.mem_iUnion.mp hi).choose else 0
  have hindex (i : ℕ) (hi : i ∈ finiteFrontLimit f) : i ∈ f (index i) := by
    simpa only [index, dif_pos hi] using (Set.mem_iUnion.mp hi).choose_spec
  let N := hfin.toFinset.sup index
  refine ⟨N, ?_⟩
  intro n i hi
  have hiL : i ∈ finiteFrontLimit f := finiteFront_subset_limit f n hi
  apply hf (show index i ≤ N from Finset.le_sup (f := index)
    (hfin.mem_toFinset.mpr hiL))
  exact hindex i hiL

section Run

variable (F : Set ℕ → Finset ℕ) (hF : IsLocallyConstantFiniteAssignment F)
  (N : Set ℕ) (hN : N.Infinite)

local notation "q" => twoFrontMatchRun F hF N hN

theorem twoFrontMatchRun_monoA : Monotone (fun n => (q n).frontA) := by
  apply monotone_nat_of_le_succ
  intro n
  have heq := congrArg Prod.fst (twoFrontMatchNext_fronts F hF (q n))
  dsimp only at heq
  change (q n).frontA ⊆ (twoFrontMatchNext F hF (q n)).frontA
  rw [heq]
  exact matchingFrontStep_monoA _ _ _ _ _ _

theorem twoFrontMatchRun_monoB : Monotone (fun n => (q n).frontB) := by
  apply monotone_nat_of_le_succ
  intro n
  have heq := congrArg Prod.snd (twoFrontMatchNext_fronts F hF (q n))
  dsimp only at heq
  change (q n).frontB ⊆ (twoFrontMatchNext F hF (q n)).frontB
  rw [heq]
  exact matchingFrontStep_monoB _ _ _ _ _ _

theorem twoFrontMatchRun_antitoneTail : Antitone (fun n => (q n).tail) := by
  apply antitone_nat_of_succ_le
  intro n
  exact fun i hi => (twoFrontMatchNext_tail F hF (q n) hi).1

theorem twoFrontMatchRunX_strictMono : StrictMono (fun n => twoFrontMatchX (q n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hx := twoFrontMatchX_mem (q (n + 1))
  have hy := (twoFrontMatchNext_tail F hF (q n) hx).2
  exact (twoFrontMatchY_spec (q n)).2.trans hy

theorem twoFrontMatchRun_limit_union_infinite :
    (finiteFrontLimit (fun n => (q n).frontA) ∪
      finiteFrontLimit (fun n => (q n).frontB)).Infinite := by
  have hX := Set.infinite_range_of_injective (twoFrontMatchRunX_strictMono F hF N hN).injective
  apply hX.mono
  rintro i ⟨n, rfl⟩
  have hmem := matchingFrontStep_mem_union (q n).colorA (q n).colorB
    (q n).frontA (q n).frontB (twoFrontMatchX (q n)) (twoFrontMatchY (q n))
  have heq := twoFrontMatchNext_fronts F hF (q n)
  rw [← heq] at hmem
  rcases Finset.mem_union.mp hmem with hA | hB
  · exact Or.inl (finiteFront_subset_limit _ (n + 1) hA)
  · exact Or.inr (finiteFront_subset_limit _ (n + 1) hB)

theorem twoFrontMatchRun_futureA (n k : ℕ) :
    ((q (n + k)).frontA : Set ℕ) ⊆ (q n).frontA ∪ (q n).tail := by
  induction k with
  | zero => simpa only [Nat.add_zero] using (Set.subset_union_left :
      ((q n).frontA : Set ℕ) ⊆ (q n).frontA ∪ (q n).tail)
  | succ k ih =>
    have htail := twoFrontMatchRun_antitoneTail F hF N hN (Nat.le_add_right n k)
    have hx := htail (twoFrontMatchX_mem (q (n + k)))
    have heq := congrArg Prod.fst (twoFrontMatchNext_fronts F hF (q (n + k)))
    dsimp only at heq
    intro i hi
    change i ∈ (twoFrontMatchNext F hF (q (n + k))).frontA at hi
    rw [heq] at hi
    cases ha : (q (n + k)).colorA <;> cases hb : (q (n + k)).colorB <;>
      simp only [matchingFrontStep, ha, hb] at hi
    all_goals first
      | exact ih hi
      | rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inr hx
        · exact ih hi

theorem twoFrontMatchRun_futureB (n k : ℕ) :
    ((q (n + k)).frontB : Set ℕ) ⊆ (q n).frontB ∪ (q n).tail := by
  induction k with
  | zero => simpa only [Nat.add_zero] using (Set.subset_union_left :
      ((q n).frontB : Set ℕ) ⊆ (q n).frontB ∪ (q n).tail)
  | succ k ih =>
    have htail := twoFrontMatchRun_antitoneTail F hF N hN (Nat.le_add_right n k)
    have hx := htail (twoFrontMatchX_mem (q (n + k)))
    have hy := htail (twoFrontMatchY_spec (q (n + k))).1
    have heq := congrArg Prod.snd (twoFrontMatchNext_fronts F hF (q (n + k)))
    dsimp only at heq
    intro i hi
    change i ∈ (twoFrontMatchNext F hF (q (n + k))).frontB at hi
    rw [heq] at hi
    cases ha : (q (n + k)).colorA <;> cases hb : (q (n + k)).colorB <;>
      simp only [matchingFrontStep, ha, hb] at hi
    all_goals first
      | exact ih hi
      | rcases Finset.mem_insert.mp hi with rfl | hi
        · first | exact Or.inr hx | exact Or.inr hy
        · exact ih hi

theorem twoFrontMatchRun_limitA_tail (n : ℕ) :
    finiteFrontLimit (fun n => (q n).frontA) \ (q n).frontA ⊆ (q n).tail := by
  rintro i ⟨hi, hnot⟩
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hi
  by_cases hmn : m ≤ n
  · exact False.elim (hnot (twoFrontMatchRun_monoA F hF N hN hmn hm))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show n ≤ m by omega)
    exact (twoFrontMatchRun_futureA F hF N hN n k hm).resolve_left hnot

theorem twoFrontMatchRun_limitB_tail (n : ℕ) :
    finiteFrontLimit (fun n => (q n).frontB) \ (q n).frontB ⊆ (q n).tail := by
  rintro i ⟨hi, hnot⟩
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hi
  by_cases hmn : m ≤ n
  · exact False.elim (hnot (twoFrontMatchRun_monoB F hF N hN hmn hm))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show n ≤ m by omega)
    exact (twoFrontMatchRun_futureB F hF N hN n k hm).resolve_left hnot

end Run

end SurveyStatements.P1
