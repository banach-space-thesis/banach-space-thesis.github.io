import Sigma.ComplexFunctionSpaces

/-! Further checked facts about the actual averaging projection. -/
noncomputable section
namespace SigmaNonprimarity

/-- The complementary antisymmetric projection. -/
def complexAntiAverage : ComplexAmbient →L[ℂ] ComplexAmbient := ContinuousLinearMap.id ℂ ComplexAmbient - complexAverage

@[simp] theorem complexAntiAverage_apply (f : ComplexAmbient) (p : Point) :
    complexAntiAverage f p = (f p - f (p.1, !p.2)) / 2 := by
  change f p - complexAverage f p = _
  rw [complexAverage_apply]
  ring

theorem complexAntiAverage_norm_le (f : ComplexAmbient) : ‖complexAntiAverage f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  intro p
  rw [complexAntiAverage_apply, norm_div, Complex.norm_ofNat]
  have h := norm_sub_le (f p) (f (p.1, !p.2))
  have h₁ := f.norm_coe_le_norm p
  have h₂ := f.norm_coe_le_norm (p.1, !p.2)
  linarith

theorem complexAverage_complexAntiAverage (f : ComplexAmbient) : complexAverage (complexAntiAverage f) = 0 := by
  change complexAverage (f - complexAverage f) = 0
  rw [map_sub, complexAverage_idempotent, sub_self]

theorem complexAntiAverage_idempotent (f : ComplexAmbient) : complexAntiAverage (complexAntiAverage f) = complexAntiAverage f := by
  change complexAntiAverage f - complexAverage (complexAntiAverage f) = complexAntiAverage f
  rw [complexAverage_complexAntiAverage, sub_zero]

theorem complexAverage_add_complexAntiAverage (f : ComplexAmbient) : complexAverage f + complexAntiAverage f = f := by
  change complexAverage f + (f - complexAverage f) = f
  simp only [sub_eq_add_neg, ← add_assoc, add_comm (complexAverage f) f, add_neg_cancel_right]

theorem complexAverage_norm_one : ‖complexAverage‖ = 1 := by
  have upper : ‖complexAverage‖ ≤ 1 := complexAverage.opNorm_le_bound (by norm_num)
    (by intro f; simpa using complexAverage_norm_le f)
  let c : ComplexAmbient := BoundedContinuousFunction.const Point 1
  have hc : ‖c‖ = 1 := by simp [c, BoundedContinuousFunction.norm_const_eq]
  have hfix : complexAverage c = c := (complexAverage_eq_self_iff c).2 (fun _ => rfl)
  have lower := complexAverage.le_opNorm c
  rw [hfix, hc, mul_one] at lower
  exact le_antisymm upper lower

theorem complexCharacteristic_singleton_mem_ComplexJL (B : Set (Set Point)) (p : Point) :
    complexCharacteristic {p} ∈ ComplexJL B := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact Or.inl (Or.inl ⟨p, rfl⟩)

/-- The antisymmetric unit vectors used to choose the diagonal evaluations
are members of the actual Y = ComplexJL(B) ∩ ker P, for every B. -/
theorem complex_fibre_difference_mem (B : Set (Set Point)) (n : ℕ) :
    complexCharacteristic {(n, false)} - complexCharacteristic {(n, true)} ∈ complexAntisymmetricJL B := by
  constructor
  · exact (ComplexJL B).sub_mem (complexCharacteristic_singleton_mem_ComplexJL B _) (complexCharacteristic_singleton_mem_ComplexJL B _)
  · change complexAverage _ = 0
    apply (complexAverage_eq_zero_iff _).2
    intro k
    change complexCharacteristic {(n, false)} (k, false) - complexCharacteristic {(n, true)} (k, false) =
      -(complexCharacteristic {(n, false)} (k, true) - complexCharacteristic {(n, true)} (k, true))
    simp only [complexCharacteristic_apply, Set.mem_singleton_iff, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, if_false, sub_zero, zero_sub,
      neg_neg]

end SigmaNonprimarity


