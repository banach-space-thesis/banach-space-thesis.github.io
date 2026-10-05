import ThesisCommon.Analysis.GowersMaureyInterpolationProfiles

/-! Elementary analytic estimates for the finite factorization costs in
the interpolation construction. These precede the source's separated-size
and factorial argument; no interpolation value is assumed. -/
noncomputable section
namespace ThesisCommon.GowersMaurey

theorem logarithmicWeight_sq_le {x : ℝ} (hx : 0 ≤ x) :
    logarithmicWeight (x^2) ≤ 2 * logarithmicWeight x := by
  have hp : 0 < x + 1 := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < x^2 + 1)
    (show x^2 + 1 ≤ (x + 1)^2 by nlinarith)
  rw [Real.log_pow] at hlog
  unfold logarithmicWeight
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have heq : (2 * (Real.log (x + 1) / Real.log 2)) * Real.log 2 =
      2 * Real.log (x + 1) := by field_simp
  rw [heq]
  simpa using hlog

theorem logarithmicWeight_le_twice_sqrt {x : ℝ} (hx : 0 ≤ x) :
    logarithmicWeight x ≤ 2 * logarithmicWeight (Real.sqrt x) := by
  simpa only [Real.sq_sqrt hx] using logarithmicWeight_sq_le (Real.sqrt_nonneg x)

theorem list_logarithmicWeight_prod_le {l : List ℝ} (hl : ∀ t ∈ l, 1 ≤ t) :
    logarithmicWeight l.prod ≤ (l.map logarithmicWeight).prod := by
  induction l with
  | nil => simp [logarithmicWeight_one]
  | cons t l ih =>
    have ht := hl t (List.mem_cons_self ..)
    have htail : ∀ s ∈ l, 1 ≤ s := fun s hs => hl s (List.mem_cons_of_mem _ hs)
    simp only [List.prod_cons, List.map_cons]
    exact (logarithmicWeight_submultiplicative ht (list_prod_ge_one htail)).trans
      (mul_le_mul_of_nonneg_left (ih htail) (zero_le_one.trans (one_le_logarithmicWeight_real ht)))

theorem list_factor_cost_ge_member {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    {l : List ℝ} (hl : ∀ t ∈ l, 1 ≤ t) {t : ℝ} (ht : t ∈ l) :
    φ t ≤ (l.map φ).prod := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    have ha := hφ a (hl a (List.mem_cons_self ..))
    have htail : ∀ s ∈ l, 1 ≤ s := fun s hs => hl s (List.mem_cons_of_mem _ hs)
    have hp : 1 ≤ (l.map φ).prod := by
      apply list_prod_ge_one
      intro y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
      exact hφ s (htail s hs)
    simp only [List.mem_cons] at ht
    simp only [List.map_cons, List.prod_cons]
    rcases ht with rfl | ht
    · exact le_mul_of_one_le_right (zero_le_one.trans ha) hp
    · exact (ih htail ht).trans (le_mul_of_one_le_left (zero_le_one.trans hp) ha)

theorem list_filter_cost_partition (φ : ℝ → ℝ) (P : ℝ → Prop) [DecidablePred P] (l : List ℝ) :
    ((l.filter P).map φ).prod * ((l.filter (fun t => ¬ P t)).map φ).prod = (l.map φ).prod := by
  induction l with
  | nil => simp
  | cons t l ih =>
    by_cases ht : P t
    · simpa [ht, mul_assoc] using congrArg (fun z => φ t * z) ih
    · simpa [ht, mul_assoc, mul_left_comm] using congrArg (fun z => φ t * z) ih

theorem sqrt_le_factor_of_small_other_product {x y B : ℝ}
    (hx : 1 ≤ x) (hy : 0 ≤ y) (hprod : x ≤ y * B) (hB : B ≤ Real.sqrt x) :
    Real.sqrt x ≤ y := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hsq := Real.sq_sqrt (zero_le_one.trans hx)
  have hh := hprod.trans (mul_le_mul_of_nonneg_left hB hy)
  nlinarith

end ThesisCommon.GowersMaurey
