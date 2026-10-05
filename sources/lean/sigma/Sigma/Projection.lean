import Sigma.FunctionSpaces

/-! Further checked facts about the actual averaging projection. -/
noncomputable section
namespace SigmaNonprimarity

/-- The complementary antisymmetric projection. -/
def antiAverage : Ambient →L[ℝ] Ambient := ContinuousLinearMap.id ℝ Ambient - average

@[simp] theorem antiAverage_apply (f : Ambient) (p : Point) :
    antiAverage f p = (f p - f (p.1, !p.2)) / 2 := by
  change f p - average f p = _
  rw [average_apply]
  ring

theorem antiAverage_norm_le (f : Ambient) : ‖antiAverage f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  intro p
  rw [antiAverage_apply, norm_div, Real.norm_ofNat]
  have h := norm_sub_le (f p) (f (p.1, !p.2))
  have h₁ := f.norm_coe_le_norm p
  have h₂ := f.norm_coe_le_norm (p.1, !p.2)
  linarith

theorem average_antiAverage (f : Ambient) : average (antiAverage f) = 0 := by
  change average (f - average f) = 0
  rw [map_sub, average_idempotent, sub_self]

theorem antiAverage_idempotent (f : Ambient) : antiAverage (antiAverage f) = antiAverage f := by
  change antiAverage f - average (antiAverage f) = antiAverage f
  rw [average_antiAverage, sub_zero]

theorem average_add_antiAverage (f : Ambient) : average f + antiAverage f = f := by
  change average f + (f - average f) = f
  simp only [sub_eq_add_neg, ← add_assoc, add_comm (average f) f, add_neg_cancel_right]

theorem average_norm_one : ‖average‖ = 1 := by
  have upper : ‖average‖ ≤ 1 := average.opNorm_le_bound (by norm_num)
    (by intro f; simpa using average_norm_le f)
  let c : Ambient := BoundedContinuousFunction.const Point 1
  have hc : ‖c‖ = 1 := by simp [c, BoundedContinuousFunction.norm_const_eq]
  have hfix : average c = c := (average_eq_self_iff c).2 (fun _ => rfl)
  have lower := average.le_opNorm c
  rw [hfix, hc, mul_one] at lower
  exact le_antisymm upper lower

theorem characteristic_singleton_mem_JL (B : Set (Set Point)) (p : Point) :
    characteristic {p} ∈ JL B := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact Or.inl (Or.inl ⟨p, rfl⟩)

/-- The antisymmetric unit vectors used to choose the diagonal evaluations
are members of the actual Y = JL(B) ∩ ker P, for every B. -/
theorem fibre_difference_mem (B : Set (Set Point)) (n : ℕ) :
    characteristic {(n, false)} - characteristic {(n, true)} ∈ antisymmetricJL B := by
  constructor
  · exact (JL B).sub_mem (characteristic_singleton_mem_JL B _) (characteristic_singleton_mem_JL B _)
  · change average _ = 0
    apply (average_eq_zero_iff _).2
    intro k
    change characteristic {(n, false)} (k, false) - characteristic {(n, true)} (k, false) =
      -(characteristic {(n, false)} (k, true) - characteristic {(n, true)} (k, true))
    simp only [characteristic_apply, Set.mem_singleton_iff, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, if_false, sub_zero, zero_sub,
      neg_neg]

end SigmaNonprimarity
