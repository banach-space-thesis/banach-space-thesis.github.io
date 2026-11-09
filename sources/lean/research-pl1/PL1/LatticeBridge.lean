import PL1.LatticeDefinitions
import BanLat.Normed
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Order.Lattice

/-!
Transporting a Banach lattice norm along a continuous linear equivalence shows
that the renorming obstruction covers target lattices in every universe.
-/

noncomputable section

universe u v

namespace PL1

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [Lattice F]
  [IsOrderedAddMonoid F] [BanachLattice F]

/-- Any real linear Banach-space isomorphism with a Banach lattice pulls back
an equivalent solid lattice norm, irrespective of the target's universe. -/
theorem hasEquivalentRealLatticeNorm_of_continuousLinearEquiv
    (e : E ≃L[ℝ] F) : HasEquivalentRealLatticeNorm E := by
  let : Lattice E := e.toEquiv.lattice
  let : IsOrderedAddMonoid E := {
    add_le_add_left := by
      intro x y h z
      change e (x + z) ≤ e (y + z)
      change e x ≤ e y at h
      simpa only [map_add] using add_le_add h (le_refl (e z)) }
  let : PosSMulMono ℝ E := {
    smul_le_smul_of_nonneg_left := by
      intro a ha x y h
      change e (a • x) ≤ e (a • y)
      change e x ≤ e y at h
      simpa only [map_smul] using smul_le_smul_of_nonneg_left h ha }
  have h_abs (x : E) : e |x| = |e x| := by
    change e (e.symm (e x ⊔ e (-x))) = |e x|
    simp only [e.apply_symm_apply, map_neg, abs]
  refine ⟨inferInstance, inferInstance, inferInstance,
    (normSeminorm ℝ F).comp e.toLinearMap, ?_,
    (‖e.symm.toContinuousLinearMap‖ + 1)⁻¹,
    ‖e.toContinuousLinearMap‖ + 1, ?_, ?_, ?_⟩
  · intro x y h
    change ‖e x‖ ≤ ‖e y‖
    apply norm_le_norm_of_abs_le_abs
    change e |x| ≤ e |y| at h
    simpa only [h_abs] using h
  · positivity
  · positivity
  · intro x
    change (‖e.symm.toContinuousLinearMap‖ + 1)⁻¹ * ‖x‖ ≤ ‖e x‖ ∧
      ‖e x‖ ≤ (‖e.toContinuousLinearMap‖ + 1) * ‖x‖
    constructor
    · have h := e.symm.toContinuousLinearMap.le_opNorm (e x)
      have hbound : ‖x‖ ≤ (‖e.symm.toContinuousLinearMap‖ + 1) * ‖e x‖ := by
        simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
          h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (norm_nonneg (e x)))
      have hpos : 0 < ‖e.symm.toContinuousLinearMap‖ + 1 := by positivity
      rw [inv_mul_eq_div, div_le_iff₀ hpos]
      simpa only [mul_comm] using hbound
    · exact (e.toContinuousLinearMap.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg x))

/-- Negating the renorming predicate rules out every real Banach lattice
target, with no restriction on its carrier universe. -/
theorem not_nonempty_continuousLinearEquiv_of_not_hasEquivalentRealLatticeNorm
    (hE : ¬ HasEquivalentRealLatticeNorm E) : ¬ Nonempty (E ≃L[ℝ] F) := by
  rintro ⟨e⟩
  exact hE (hasEquivalentRealLatticeNorm_of_continuousLinearEquiv e)

end PL1
