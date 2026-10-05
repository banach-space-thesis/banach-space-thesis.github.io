import Posets.BipartiteCount
import Mathlib.Data.Nat.Choose.Sum

/-! The antichain and complete-bipartite examples following Proposition 8.4.
These count the same interval upsets as `idealCount`, whose equivalence with
actual closed incidence-algebra ideals is proved in IncidenceIdealClosed. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set
open scoped BigOperators
namespace Posets

theorem paper_antichain_idealCount (P : Type) [PartialOrder P] [Fintype P]
    (hanti : ∀ a b : P, a ≤ b → a = b) : idealCount P = 2 ^ Fintype.card P := by
  let Q := {st : P × P // st.1 ≤ st.2}
  let e : IntervalUpsets P ≃ Set Q :=
    { toFun := Subtype.val
      invFun := fun W => ⟨W, by
        intro i hi j hji hij
        have heq : j = i := by
          apply Subtype.ext
          exact Prod.ext (hanti _ _ hji) (hanti _ _ hij).symm
        simpa only [heq] using hi⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let q : Q ≃ P :=
    { toFun := fun i => i.val.1
      invFun := fun p => ⟨(p, p), le_rfl⟩
      left_inv := fun i => by
        apply Subtype.ext
        exact Prod.ext rfl (hanti _ _ i.property)
      right_inv := fun _ => rfl }
  rw [idealCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_set,
    Fintype.card_congr q]

private theorem sum_finsets_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ I : Finset (Fin n), f I.card) =
      ∑ i ∈ Finset.range (n + 1), n.choose i * f i := by
  simpa using (Finset.sum_powerset_apply_card f (x := (Finset.univ : Finset (Fin n))))

private theorem explicit_product_card {A B : Type} (I : Finset A) (J : Finset B) :
    (Finset.product I J).card = I.card * J.card := Finset.card_product I J

/-- Complete-bipartite instance of the paper's count, using its actual poset. -/
def paperCompleteBipartiteCount (p q : ℕ) : ℕ :=
  @idealCount (Fin p ⊕ Fin q) (bipartiteOrder (fun _ _ => True)) inferInstance

theorem paper_complete_bipartite_double_sum (p q : ℕ) :
    paperCompleteBipartiteCount p q =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        p.choose i * q.choose j * 2 ^ (i * j) := by
  have h := proposition_8_5_proof (fun (_ : Fin p) (_ : Fin q) => True)
  change paperCompleteBipartiteCount p q = _ at h
  simp only [Finset.filter_true] at h
  simp_rw [explicit_product_card] at h
  rw [h]
  have hinner (I : Finset (Fin p)) :
      (∑ J : Finset (Fin q), 2 ^ (I.card * J.card)) =
        ∑ j ∈ Finset.range (q + 1), q.choose j * 2 ^ (I.card * j) :=
    sum_finsets_card q (fun j => 2 ^ (I.card * j))
  simp_rw [hinner]
  rw [sum_finsets_card p (fun i => ∑ j ∈ Finset.range (q + 1), q.choose j * 2 ^ (i * j))]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem paper_complete_bipartite_sum (p q : ℕ) :
    paperCompleteBipartiteCount p q =
      ∑ i ∈ Finset.range (p + 1), p.choose i * (1 + 2 ^ i) ^ q := by
  rw [paper_complete_bipartite_double_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_comm 1, add_pow]
  simp only [one_pow, mul_one, ← pow_mul, Nat.cast_id]
  simp_rw [Finset.mul_sum, mul_assoc, mul_comm (q.choose _) (2 ^ (_ * _))]

theorem paper_star_count (q : ℕ) : paperCompleteBipartiteCount 1 q = 2 ^ q + 3 ^ q := by
  rw [paper_complete_bipartite_sum]
  norm_num [Finset.sum_range_succ]

theorem paper_two_by_q_count (q : ℕ) :
    paperCompleteBipartiteCount 2 q = 2 ^ q + 2 * 3 ^ q + 5 ^ q := by
  rw [paper_complete_bipartite_sum]
  norm_num [Finset.sum_range_succ]

theorem paper_star_examples :
    paperCompleteBipartiteCount 1 1 = 5 ∧ paperCompleteBipartiteCount 1 2 = 13 ∧
      paperCompleteBipartiteCount 1 3 = 35 ∧ paperCompleteBipartiteCount 1 4 = 97 := by
  norm_num [paper_star_count]

theorem paper_two_by_q_examples :
    paperCompleteBipartiteCount 2 2 = 47 ∧ paperCompleteBipartiteCount 2 3 = 187 ∧
      paperCompleteBipartiteCount 2 4 = 803 := by
  norm_num [paper_two_by_q_count]

end Posets
