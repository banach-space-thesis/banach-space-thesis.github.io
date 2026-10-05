import ThesisCommon.Analysis.LatticeDisjointness
import Mathlib.Algebra.Order.Group.PosPart

/-! Lift a positive fragment of a modulus with the original element's sign.
The construction and both modulus identities hold in any lattice ordered
additive commutative group. -/

namespace ThesisCommon
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

/-- Split a positive fragment along the positive and negative parts. -/
def latticeSignLift (x y : E) : E := (y ⊓ x⁺) - (y ⊓ x⁻)

theorem lattice_sign_components_sum (x : E) {y : E} (hy0 : 0 ≤ y) (hy : y ≤ |x|) :
    (y ⊓ x⁺) + (y ⊓ x⁻) = y := by
  letI : DistribLattice E := AddCommGroup.toDistribLattice E
  have hinf : (y ⊓ x⁺) ⊓ (y ⊓ x⁻) = 0 := by
    apply le_antisymm
    · exact (inf_le_inf inf_le_right inf_le_right).trans_eq (posPart_inf_negPart_eq_zero x)
    · exact le_inf (le_inf hy0 (posPart_nonneg x)) (le_inf hy0 (negPart_nonneg x))
  have hsup : x⁺ ⊔ x⁻ = |x| := by
    calc
      x⁺ ⊔ x⁻ = 0 + (x⁺ ⊔ x⁻) := (zero_add _).symm
      _ = (x⁺ ⊓ x⁻) + (x⁺ ⊔ x⁻) := by rw [posPart_inf_negPart_eq_zero]
      _ = x⁺ + x⁻ := inf_add_sup _ _
      _ = |x| := posPart_add_negPart x
  calc
    (y ⊓ x⁺) + (y ⊓ x⁻) = ((y ⊓ x⁺) ⊓ (y ⊓ x⁻)) +
        ((y ⊓ x⁺) ⊔ (y ⊓ x⁻)) := (inf_add_sup _ _).symm
    _ = y := by rw [hinf, zero_add, ← inf_sup_left, hsup, inf_eq_left.mpr hy]

theorem abs_latticeSignLift (x : E) {y : E} (hy0 : 0 ≤ y) (hy : y ≤ |x|) :
    |latticeSignLift x y| = y := by
  have ha : 0 ≤ y ⊓ x⁺ := le_inf hy0 (posPart_nonneg x)
  have hb : 0 ≤ y ⊓ x⁻ := le_inf hy0 (negPart_nonneg x)
  have hdisj : |y ⊓ x⁺| ⊓ |y ⊓ x⁻| = 0 := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    exact le_antisymm
      ((inf_le_inf inf_le_right inf_le_right).trans_eq (posPart_inf_negPart_eq_zero x))
      (le_inf ha hb)
  rw [latticeSignLift, lattice_abs_sub_of_disjoint hdisj, abs_of_nonneg ha, abs_of_nonneg hb]
  exact lattice_sign_components_sum x hy0 hy

theorem abs_sub_latticeSignLift (x : E) {y : E} (hy0 : 0 ≤ y) (hy : y ≤ |x|) :
    |x - latticeSignLift x y| = |x| - y := by
  have ha : 0 ≤ x⁺ - (y ⊓ x⁺) := sub_nonneg.mpr inf_le_right
  have hb : 0 ≤ x⁻ - (y ⊓ x⁻) := sub_nonneg.mpr inf_le_right
  have hdisj : |x⁺ - (y ⊓ x⁺)| ⊓ |x⁻ - (y ⊓ x⁻)| = 0 := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    apply le_antisymm
    · exact (inf_le_inf
        (sub_le_self _ (le_inf hy0 (posPart_nonneg x)))
        (sub_le_self _ (le_inf hy0 (negPart_nonneg x)))).trans_eq (posPart_inf_negPart_eq_zero x)
    · exact le_inf ha hb
  have heq : x - latticeSignLift x y =
      (x⁺ - (y ⊓ x⁺)) - (x⁻ - (y ⊓ x⁻)) := by
    rw [latticeSignLift]
    calc
      x - ((y ⊓ x⁺) - (y ⊓ x⁻)) =
          (x⁺ - x⁻) - ((y ⊓ x⁺) - (y ⊓ x⁻)) := by rw [posPart_sub_negPart]
      _ = _ := by abel
  rw [heq, lattice_abs_sub_of_disjoint hdisj, abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    (x⁺ - (y ⊓ x⁺)) + (x⁻ - (y ⊓ x⁻)) =
        (x⁺ + x⁻) - ((y ⊓ x⁺) + (y ⊓ x⁻)) := by abel
    _ = |x| - y := by rw [posPart_add_negPart, lattice_sign_components_sum x hy0 hy]

end ThesisCommon
