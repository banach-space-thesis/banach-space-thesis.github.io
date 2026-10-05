import ThesisCommon.Analysis.GowersMaureyFactorNormalization
import ThesisCommon.Analysis.FiniteFactorProductBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Product bounds for the actual rapidly separated construction sizes.
These use the sequence itself, without replacing all earlier sizes by all
integers below the last size. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
local instance : DecidableEq ℝ := Classical.decEq ℝ

theorem pow_eight_le_exp_twice {x : ℝ} (hx : 64 ≤ x) :
    x ^ 8 ≤ Real.exp (2 * x) := by
  have hx0 : 0 ≤ x := by linarith
  have hbase : x ≤ (x / 8 + 1) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ x - 64 by linarith) hx0]
  have hexp : x ≤ Real.exp (x / 4) := by
    calc
      x ≤ (x / 8 + 1) ^ 2 := hbase
      _ ≤ (Real.exp (x / 8)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp (x / 4) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    x ^ 8 ≤ (Real.exp (x / 4)) ^ 8 := pow_le_pow_left₀ hx0 hexp _
    _ = Real.exp (2 * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

namespace ConstructionData
variable {𝕜 : Type*} [RCLike 𝕜] (D : ConstructionData 𝕜)

theorem one_le_size (n : ℕ) : (1 : ℝ) ≤ D.j n := by
  exact_mod_cast (Nat.succ_le_iff.mpr (D.j_positive n))

theorem size_large (n : ℕ) : (256 : ℝ) < D.j n := by
  have hfirst : (256 : ℝ) < D.j 0 :=
    D.first_large.trans_le (logarithmicWeight_le_self_real (D.one_le_size 0))
  exact hfirst.trans_le (by exact_mod_cast D.j_strict.monotone (Nat.zero_le n))

theorem loglog_size_pos (n : ℕ) : 0 < Real.log (Real.log (D.j n : ℝ)) := by
  apply Real.log_pos
  apply (Real.lt_log_iff_exp_lt (by exact_mod_cast D.j_positive n : (0 : ℝ) < D.j n)).mpr
  have h := D.size_large n
  exact Real.exp_one_lt_d9.trans (by linarith)

theorem exp_twice_size_lt_loglog {m n : ℕ} (hmn : m < n) :
    Real.exp (2 * (D.j m : ℝ)) < Real.log (Real.log (D.j n : ℝ)) :=
  (Real.lt_log_iff_exp_lt (D.loglog_size_pos n)).mp (D.rapid m n hmn)

theorem size_pow_eight_lt_loglog {m n : ℕ} (hmn : m < n) :
    (D.j m : ℝ) ^ 8 < Real.log (Real.log (D.j n : ℝ)) :=
  (pow_eight_le_exp_twice (by have h := D.size_large m; linarith)).trans_lt
    (D.exp_twice_size_lt_loglog hmn)

theorem size_sq_le_of_lt {m n : ℕ} (hmn : m < n) :
    (D.j m : ℝ) ^ 2 ≤ D.j n := by
  have hm0 : (0 : ℝ) ≤ D.j m := by positivity
  have hn0 : (0 : ℝ) ≤ D.j n := by positivity
  have hlog : 0 ≤ Real.log (D.j n : ℝ) := Real.log_nonneg (D.one_le_size n)
  have hs : (D.j m : ℝ) ^ 2 ≤ Real.exp (2 * (D.j m : ℝ)) := by
    have he : (D.j m : ℝ) ≤ Real.exp (D.j m : ℝ) :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    calc
      _ ≤ (Real.exp (D.j m : ℝ)) ^ 2 := pow_le_pow_left₀ hm0 he 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  exact hs.trans ((D.exp_twice_size_lt_loglog hmn).le.trans
    ((Real.log_le_self hlog).trans (Real.log_le_self hn0)))

theorem prod_sizes_le_square (n : ℕ) :
    (∏ i ∈ Finset.range (n + 1), (D.j i : ℝ)) ≤ (D.j n : ℝ) ^ 2 := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.prod_range_one]
    have h := D.one_le_size 0
    nlinarith
  | succ n ih =>
    rw [Finset.prod_range_succ]
    calc
      _ ≤ (D.j n : ℝ) ^ 2 * D.j (n+1) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ (D.j (n+1) : ℝ) * D.j (n+1) :=
        mul_le_mul_of_nonneg_right (D.size_sq_le_of_lt (Nat.lt_succ_self n)) (by positivity)
      _ = _ := by ring

theorem list_prod_le_size_fourth (n : ℕ) (l : List ℝ)
    (hmem : ∀ x ∈ l, ∃ i ≤ n, x = (D.j i : ℝ))
    (hcount : ∀ x ∈ l, l.count x ≤ 2) :
    l.prod ≤ (D.j n : ℝ) ^ 4 := by
  let r := (Finset.range (n+1)).toList.map (fun i => (D.j i : ℝ))
  have hi : Function.Injective (fun i => (D.j i : ℝ)) :=
    Nat.cast_injective.comp D.j_strict.injective
  have hr : r.Nodup := (Finset.nodup_toList _).map hi
  have hsub : l ⊆ r := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hmem x hx
    exact List.mem_map.mpr ⟨i, by simpa using Nat.lt_succ_of_le hi, rfl⟩
  have hge : ∀ x ∈ r, 1 ≤ x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact D.one_le_size i
  have hprod : r.prod ≤ (D.j n : ℝ) ^ 2 := by
    simpa only [r, Finset.prod_map_toList] using D.prod_sizes_le_square n
  calc
    l.prod ≤ r.prod ^ 2 := realList_prod_le_square_of_count_le_two l r hr hsub hge hcount
    _ ≤ ((D.j n : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (zero_le_one.trans (list_prod_ge_one hge)) hprod _
    _ = _ := by ring

theorem list_prod_sq_lt_loglog {m n : ℕ} (hmn : m < n) (l : List ℝ)
    (hmem : ∀ x ∈ l, ∃ i ≤ m, x = (D.j i : ℝ))
    (hcount : ∀ x ∈ l, l.count x ≤ 2) :
    l.prod ^ 2 < Real.log (Real.log (D.j n : ℝ)) := by
  have hl : ∀ x ∈ l, 1 ≤ x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := hmem x hx
    exact D.one_le_size i
  have h := pow_le_pow_left₀ (zero_le_one.trans (list_prod_ge_one hl))
    (D.list_prod_le_size_fourth m l hmem hcount) 2
  have he : ((D.j m : ℝ) ^ 4) ^ 2 = (D.j m : ℝ) ^ 8 := by ring
  rw [he] at h
  exact h.trans_lt (D.size_pow_eight_lt_loglog hmn)

end ConstructionData
end ThesisCommon.GowersMaurey
