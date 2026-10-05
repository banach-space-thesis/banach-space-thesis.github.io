import ThesisCommon.Analysis.RegularizedSubmultiplicativeProfile

/-! Lower barriers survive both stages of the actual regularization
when their reciprocal extension is concave. Equality is consequently
preserved at every point where the seed touches that barrier. -/
noncomputable section
namespace ThesisCommon

theorem concavifiedReciprocal_le_barrier {φ β : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x)
    (hβ : ∀ x, 1 ≤ x → 1 ≤ β x) (hβone : β 1 ≤ 1)
    (hmono : MonotoneOn β (Set.Ici 1))
    (hmul : ∀ x y, 1 ≤ x → 1 ≤ y → β (x * y) ≤ β x * β y)
    (hβφ : ∀ x, 1 ≤ x → β x ≤ φ x)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (extendedReciprocalProfile β))
    {x : ℝ} (hx : 0 ≤ x) :
    concavifiedReciprocal φ x ≤ extendedReciprocalProfile β x := by
  apply positiveConcaveEnvelope_le_of_concave
    (fun _ hx => extendedReciprocalProfile_nonneg (fun x _ => one_le_submultiplicativeHull hφ x) hx)
    hconc _ hx
  intro t ht
  by_cases ht1 : t ≤ 1
  · simp only [extendedReciprocalProfile_of_le ht1, le_refl]
  · have htle : 1 ≤ t := le_of_not_ge ht1
    simp only [extendedReciprocalProfile, if_neg ht1]
    exact div_le_div_of_nonneg_left ht (zero_lt_one.trans_le (hβ t htle))
      (le_submultiplicativeHull hφ (fun x hx => zero_le_one.trans (hβ x hx))
        hβone hmono hmul hβφ htle)

theorem barrier_le_regularizedProfile {φ β : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1)
    (hβ : ∀ x, 1 ≤ x → 1 ≤ β x) (hβone : β 1 ≤ 1)
    (hmono : MonotoneOn β (Set.Ici 1))
    (hmul : ∀ x y, 1 ≤ x → 1 ≤ y → β (x * y) ≤ β x * β y)
    (hβφ : ∀ x, 1 ≤ x → β x ≤ φ x)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (extendedReciprocalProfile β))
    {x : ℝ} (hx : 1 ≤ x) : β x ≤ regularizedProfile φ x := by
  have hb1 : β 1 = 1 := le_antisymm hβone (hβ 1 le_rfl)
  have hh := concavifiedReciprocal_le_barrier hφ hβ hβone hmono hmul hβφ hconc (zero_le_one.trans hx)
  rw [extendedReciprocalProfile_of_one_le hb1 hx] at hh
  rw [regularizedProfile, le_div_iff₀ (concavifiedReciprocal_pos hφ hφone hx)]
  have hbpos : 0 < β x := zero_lt_one.trans_le (hβ x hx)
  simpa only [mul_comm] using (le_div_iff₀ hbpos).mp hh

theorem regularizedProfile_eq_at_barrier {φ β : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1)
    (hβ : ∀ x, 1 ≤ x → 1 ≤ β x) (hβone : β 1 ≤ 1)
    (hmono : MonotoneOn β (Set.Ici 1))
    (hmul : ∀ x y, 1 ≤ x → 1 ≤ y → β (x * y) ≤ β x * β y)
    (hβφ : ∀ x, 1 ≤ x → β x ≤ φ x)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (extendedReciprocalProfile β))
    {x : ℝ} (hx : 1 ≤ x) (heq : φ x = β x) : regularizedProfile φ x = β x := by
  apply le_antisymm
  · simpa only [heq] using regularizedProfile_le hφ hφone hx
  · exact barrier_le_regularizedProfile hφ hφone hβ hβone hmono hmul hβφ hconc hx

theorem regularizedProfile_inverse_mul {φ : ℝ → ℝ}
    (hφ : ∀ x, 1 ≤ x → 1 ≤ φ x) (hφone : φ 1 ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    (regularizedProfile φ x)⁻¹ * x = concavifiedReciprocal φ x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hG0 := (concavifiedReciprocal_pos hφ hφone hx).ne'
  unfold regularizedProfile
  field_simp

end ThesisCommon
