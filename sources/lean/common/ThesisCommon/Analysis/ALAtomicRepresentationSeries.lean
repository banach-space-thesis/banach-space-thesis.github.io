import ThesisCommon.Analysis.ALAtomicRepresentationProjection
import ThesisCommon.Analysis.DualLatticeModulus
import ThesisCommon.Analysis.LpOneRestriction
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Contractive coefficient and synthesis operators for the normalized atoms
of a complete AL-lattice. Surjectivity onto the original lattice is postponed
until the atomicity hypothesis is used in the final representation module. -/
noncomputable section
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)

theorem alAtomCoordinate_finite_abs_sum_le (s : Finset (NormalizedLatticeAtom E)) (x : E) :
    (∑ a ∈ s, ‖alAtomCoordinate hAL a x‖) ≤ ‖x‖ := by
  calc
    (∑ a ∈ s, ‖alAtomCoordinate hAL a x‖) ≤ ∑ a ∈ s, alAtomCoordinate hAL a |x| := by
      apply sum_le_sum
      intro a _
      rw [Real.norm_eq_abs]
      exact positive_functional_abs_apply_le (alAtomCoordinate_nonneg hAL a) x
    _ ≤ ‖|x|‖ := alAtomCoordinate_finite_sum_norm_le hAL s |x| (abs_nonneg x)
    _ = ‖x‖ := norm_abs_eq_norm x

theorem alAtomCoordinate_summable_norm (x : E) :
    Summable (fun a : NormalizedLatticeAtom E => ‖alAtomCoordinate hAL a x‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (fun s => alAtomCoordinate_finite_abs_sum_le hAL s x)

def alAtomCoefficients (x : E) : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1 :=
  ⟨fun a => alAtomCoordinate hAL a x, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using alAtomCoordinate_summable_norm hAL x)⟩

theorem alAtomCoefficients_norm_le (x : E) : ‖alAtomCoefficients hAL x‖ ≤ ‖x‖ := by
  rw [← (lp_one_hasSum_norm (alAtomCoefficients hAL x)).tsum_eq]
  exact (alAtomCoordinate_summable_norm hAL x).tsum_le_of_sum_le
    (fun s => alAtomCoordinate_finite_abs_sum_le hAL s x)

def alAtomCoordinates : E →L[ℝ] lp (fun _ : NormalizedLatticeAtom E => ℝ) 1 :=
  LinearMap.mkContinuous
    { toFun := alAtomCoefficients hAL
      map_add' := by intro x y; apply lp.ext; funext a; exact map_add (alAtomCoordinate hAL a) x y
      map_smul' := by intro r x; apply lp.ext; funext a; exact map_smul (alAtomCoordinate hAL a) r x }
    1 (fun x => by simpa only [one_mul] using alAtomCoefficients_norm_le hAL x)

@[simp] theorem alAtomCoordinates_apply (x : E) (a : NormalizedLatticeAtom E) :
    alAtomCoordinates hAL x a = alAtomCoordinate hAL a x := rfl

variable [CompleteSpace E]

theorem alAtomSynthesis_summable (c : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1) :
    Summable (fun a : NormalizedLatticeAtom E => c a • (a : E)) :=
  (lp_one_hasSum_norm c).summable.of_norm_bounded (fun a => by
    rw [norm_smul, a.property.2, mul_one])

def alAtomSynthesis : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1 →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun c => ∑' a : NormalizedLatticeAtom E, c a • (a : E)
      map_add' := by
        intro c d
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (alAtomSynthesis_summable c).tsum_add (alAtomSynthesis_summable d)
      map_smul' := by
        intro r c
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact (alAtomSynthesis_summable c).tsum_const_smul r }
    1 (fun c => by
      rw [one_mul]
      exact (alAtomSynthesis_summable c).hasSum.norm_le_of_bounded
        (lp_one_hasSum_norm c) (fun a => by rw [norm_smul, a.property.2, mul_one]))

@[simp] theorem alAtomSynthesis_apply (c : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1) :
    alAtomSynthesis c = ∑' a : NormalizedLatticeAtom E, c a • (a : E) := rfl

theorem alAtomSynthesis_norm_le (c : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1) :
    ‖alAtomSynthesis c‖ ≤ ‖c‖ :=
  (alAtomSynthesis_summable c).hasSum.norm_le_of_bounded
    (lp_one_hasSum_norm c) (fun a => by rw [norm_smul, a.property.2, mul_one])

theorem alAtomCoordinate_synthesis (a : NormalizedLatticeAtom E)
    (c : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1) :
    alAtomCoordinate hAL a (alAtomSynthesis c) = c a := by
  classical
  rw [alAtomSynthesis_apply, (alAtomCoordinate hAL a).map_tsum (alAtomSynthesis_summable c),
    tsum_eq_single a]
  · rw [map_smul, alAtomCoordinate_self hAL, smul_eq_mul, mul_one]
  · intro b hba
    rw [map_smul, alAtomCoordinate_other hAL a b (Ne.symm hba), smul_zero]

theorem alAtomCoordinates_synthesis (c : lp (fun _ : NormalizedLatticeAtom E => ℝ) 1) :
    alAtomCoordinates hAL (alAtomSynthesis c) = c := by
  apply lp.ext
  funext a
  exact alAtomCoordinate_synthesis hAL a c

end ThesisCommon
