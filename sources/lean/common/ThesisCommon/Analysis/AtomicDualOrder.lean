import ThesisCommon.Analysis.AtomicDualModulus
import ThesisCommon.Analysis.FunctionalAtoms

/-! An order-compatible ell-one representation of the dual has positive
atomic coordinate functionals. Their modulus identity and the countable
norming extraction then apply to the original normed vector lattice. -/
noncomputable section
namespace ThesisCommon
open scoped PositiveOperatorOrder
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

omit [HasSolidNorm E] in
theorem dualAtom_isPositiveFunctionalAtom
    (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (horder : ∀ φ : E →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i) (i : I) :
    IsPositiveFunctionalAtom (dualAtom d i) := by
  classical
  have hc : d (dualAtom d i) = lp.single (E := fun _ : I => ℝ) 1 i 1 := d.apply_symm_apply _
  have hpos : 0 ≤ dualAtom d i := by
    apply (horder _).mpr
    intro j
    rw [hc]
    by_cases hj : j = i <;> simp [hj,lp.single_apply]
  refine ⟨hpos,?_,?_⟩
  · intro hz
    have ht := congrArg (fun c : lp (fun _ : I => ℝ) 1 => c i) hc
    rw [hz,map_zero] at ht
    simp only [lp.coeFn_zero,Pi.zero_apply,lp.single_apply_self,zero_ne_one] at ht
  · intro ψ hψ hψφ
    have hp (j : I) : 0 ≤ d ψ j := (horder ψ).mp hψ j
    have hdiff : 0 ≤ dualAtom d i - ψ := sub_nonneg.mpr hψφ
    have hle (j : I) : d ψ j ≤ lp.single (E := fun _ : I => ℝ) 1 i 1 j := by
      have ht := (horder _).mp hdiff j
      rw [map_sub,hc] at ht
      exact sub_nonneg.mp ht
    refine ⟨d ψ i,hp i,?_⟩
    apply d.injective
    rw [map_smul,hc]
    apply lp.ext
    funext j
    by_cases hj : j = i
    · subst j
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply_self,mul_one]
    · have hj0 : d ψ j = 0 := le_antisymm (by simpa [lp.single_apply,Pi.single_apply,hj] using hle j) (hp j)
      simp [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply,hj,hj0]

theorem not_desiredProperty_of_ordered_dual
    (d : (E →L[ℝ] ℝ) ≃L[ℝ] lp (fun _ : I => ℝ) 1)
    (horder : ∀ φ : E →L[ℝ] ℝ, 0 ≤ φ ↔ ∀ i, 0 ≤ d φ i)
    (he : ∃ e : ℕ → E →L[ℝ] ℝ, IsNorming e) : ¬ DesiredProperty E :=
  not_desiredProperty_of_dual_atoms_abs d he (fun i x => (dualAtom_isPositiveFunctionalAtom d horder i).map_abs x)

end ThesisCommon
