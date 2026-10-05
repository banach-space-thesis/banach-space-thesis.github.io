import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic

/-! Modulus identities for disjoint elements of a lattice ordered additive group. -/

namespace ThesisCommon
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

/-- Doubling reflects order in every lattice ordered additive group. -/
theorem lattice_two_nsmul_le_two_nsmul_iff (x y : E) :
    2 • x ≤ 2 • y ↔ x ≤ y := by
  constructor
  · intro h
    apply sub_nonneg.mp
    apply nsmul_two_semiclosed
    rw [nsmul_sub]
    exact sub_nonneg.mpr h
  · intro h
    simpa only [two_nsmul] using add_le_add h h

theorem lattice_two_nsmul_injective : Function.Injective (fun x : E => 2 • x) := by
  intro x y h
  exact le_antisymm ((lattice_two_nsmul_le_two_nsmul_iff x y).mp h.le)
    ((lattice_two_nsmul_le_two_nsmul_iff y x).mp h.ge)

/-- Doubling preserves binary suprema without a total-order assumption. -/
theorem lattice_two_nsmul_sup (x y : E) :
    2 • (x ⊔ y) = (2 • x) ⊔ (2 • y) := by
  have hxy : x + y ≤ (2 • x) ⊔ (2 • y) := by
    apply (lattice_two_nsmul_le_two_nsmul_iff _ _).mp
    rw [nsmul_add, two_nsmul ((2 • x) ⊔ (2 • y))]
    exact add_le_add le_sup_left le_sup_right
  apply le_antisymm
  · simp only [two_nsmul, add_sup, sup_add]
    exact sup_le (sup_le le_sup_left (by simpa only [add_comm, two_nsmul] using hxy))
      (sup_le (by simpa only [two_nsmul] using hxy) le_sup_right)
  · exact sup_le (by simpa only [two_nsmul] using add_le_add le_sup_left le_sup_left)
      (by simpa only [two_nsmul] using add_le_add le_sup_right le_sup_right)

/-- The larger of the two signed-sum moduli is the sum of the moduli. -/
theorem lattice_abs_add_sup_abs_sub (x y : E) :
    |x + y| ⊔ |x - y| = |x| + |y| := by
  simp only [abs, sub_eq_add_neg, neg_add, neg_neg, add_sup, sup_add]
  ac_rfl

/-- The sum of the signed-sum moduli is twice the supremum of the moduli. -/
theorem lattice_abs_add_add_abs_sub (x y : E) :
    |x + y| + |x - y| = 2 • (|x| ⊔ |y|) := by
  calc
    |x + y| + |x - y| =
        ((x + y) + (x - y)) ⊔ ((x + y) + -(x - y)) ⊔
        ((-(x + y) + (x - y)) ⊔ (-(x + y) + -(x - y))) := by
      simp only [abs, add_sup, sup_add]
      ac_rfl
    _ = (2 • x) ⊔ (2 • y) ⊔ ((2 • -y) ⊔ (2 • -x)) := by
      congr 2 <;> simp only [two_nsmul] <;> abel
    _ = 2 • (|x| ⊔ |y|) := by
      simp only [abs, lattice_two_nsmul_sup]
      ac_rfl

/-- Disjointness of moduli is equivalent to equality of the sum and difference
moduli. This is an identity in the vector lattice itself, not a norm identity. -/
theorem lattice_abs_inf_abs_eq_zero_iff (x y : E) :
    |x| ⊓ |y| = 0 ↔ |x - y| = |x + y| := by
  constructor
  · intro hdisj
    have hsum : |x| + |y| = |x| ⊔ |y| := by
      simpa only [hdisj, zero_add] using (inf_add_sup |x| |y|).symm
    have hsup : |x + y| ⊔ |x - y| = |x| ⊔ |y| :=
      (lattice_abs_add_sup_abs_sub x y).trans hsum
    have hinf : |x + y| ⊓ |x - y| = |x + y| ⊔ |x - y| := by
      apply add_right_cancel (b := |x + y| ⊔ |x - y|)
      rw [inf_add_sup, lattice_abs_add_add_abs_sub, hsup, two_nsmul]
    apply le_antisymm
    · exact le_sup_right.trans (hinf.symm.le.trans inf_le_left)
    · exact le_sup_left.trans (hinf.symm.le.trans inf_le_right)
  · intro heq
    have hsum : |x| + |y| = |x| ⊔ |y| := by
      apply lattice_two_nsmul_injective
      calc
        2 • (|x| + |y|) = 2 • |x + y| := by
          rw [← lattice_abs_add_sup_abs_sub, heq, sup_idem]
        _ = |x + y| + |x - y| := by rw [heq, two_nsmul]
        _ = 2 • (|x| ⊔ |y|) := lattice_abs_add_add_abs_sub x y
    apply add_right_cancel (b := |x| ⊔ |y|)
    rw [inf_add_sup, zero_add, hsum]

/-- Modulus is additive on disjoint elements. -/
theorem lattice_abs_add_of_disjoint {x y : E} (hdisj : |x| ⊓ |y| = 0) :
    |x + y| = |x| + |y| := by
  have heq := (lattice_abs_inf_abs_eq_zero_iff x y).mp hdisj
  simpa only [heq, sup_idem] using lattice_abs_add_sup_abs_sub x y

/-- For disjoint elements, subtraction also adds the two moduli. -/
theorem lattice_abs_sub_of_disjoint {x y : E} (hdisj : |x| ⊓ |y| = 0) :
    |x - y| = |x| + |y| :=
  ((lattice_abs_inf_abs_eq_zero_iff x y).mp hdisj).trans
    (lattice_abs_add_of_disjoint hdisj)

end ThesisCommon
