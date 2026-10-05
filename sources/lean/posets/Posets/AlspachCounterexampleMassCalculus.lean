import Posets.AlspachCounterexampleProbabilityMass

/-! Positivity, support, and substitution formulas for the row masses.
These apply to arbitrary sets; openness only enters the Wolfe recursion. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachProbability
variable {K L : Type*}

theorem mass_mono (p : AlspachProbability K) {U V : Set K} (h : U ⊆ V) :
    p.mass U ≤ p.mass V := by
  induction p with
  | point k => by_cases hk : k ∈ U <;> by_cases hk' : k ∈ V <;> simp_all [mass]; exact (hk' (h hk)).elim
  | average p q hp hq => simp only [mass]; linarith

theorem mass_eq_zero (p : AlspachProbability K) (U : Set K)
    (h : ∀ k ∈ p.support, k ∉ U) : p.mass U = 0 := by
  induction p with
  | point k => simp [mass, h k (Finset.mem_singleton_self k)]
  | average p q hp hq =>
      rw [mass, hp (fun k hk => h k (Finset.mem_union_left _ hk)),
        hq (fun k hk => h k (Finset.mem_union_right _ hk))]
      simp

theorem mass_eq_one (p : AlspachProbability K) (U : Set K)
    (h : ∀ k ∈ p.support, k ∈ U) : p.mass U = 1 := by
  induction p with
  | point k => simp [mass, h k (Finset.mem_singleton_self k)]
  | average p q hp hq =>
      rw [mass, hp (fun k hk => h k (Finset.mem_union_left _ hk)),
        hq (fun k hk => h k (Finset.mem_union_right _ hk))]
      norm_num

theorem mass_eq_eval_indicator (p : AlspachProbability K) (U : Set K) :
    p.mass U = p.eval (fun k => if k ∈ U then (1 : ℝ) else 0) := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp only [mass, eval_average, hp, hq]

theorem mass_bind (p : AlspachProbability K) (f : K → AlspachProbability L) (U : Set L) :
    (p.bind f).mass U = p.eval (fun k => (f k).mass U) := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp only [bind, mass, eval_average, hp, hq]

theorem mass_pos_iff (p : AlspachProbability K) (U : Set K) :
    0 < p.mass U ↔ ∃ k ∈ p.support, k ∈ U := by
  induction p with
  | point k => by_cases hk : k ∈ U <;> simp [mass, support, hk]
  | average p q hp hq =>
      have hn₁ := p.mass_nonneg U
      have hn₂ := q.mass_nonneg U
      have he : 0 < (average p q).mass U ↔ 0 < p.mass U ∨ 0 < q.mass U := by
        simp only [mass]
        constructor
        · intro h; by_contra hn; push_neg at hn; linarith
        · rintro (h | h) <;> linarith
      rw [he, hp, hq]
      simp only [support, Finset.mem_union]
      aesop

end AlspachProbability
end Posets

