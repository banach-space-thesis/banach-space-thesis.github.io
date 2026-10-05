import ThesisCommon.Analysis.ALAtomicRepresentationSeries

/-! The ordered ell-one representation of an atomic complete real AL-lattice.
Atomicity is the only additional assumption. The coefficient and synthesis
operators are constructed, their inverses are proved, and their norms are
contractive, yielding an actual linear isometry and order equivalence. -/
noncomputable section
universe u
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
variable [CompleteSpace E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)
variable (hAtom : ∀ x : E, 0 ≤ x → x ≠ 0 → ∃ a : E, IsPositiveLatticeAtom a ∧ a ≤ x)

include hAL hAtom

/-- Every positive vector is the norm-convergent sum of its atomic
components. A nonzero positive residual would contain an omitted atom. -/
theorem alAtomSynthesis_coordinates_of_nonneg (x : E) (hx : 0 ≤ x) :
    alAtomSynthesis (alAtomCoordinates hAL x) = x := by
  let v := alAtomSynthesis (alAtomCoordinates hAL x)
  have hvx : v ≤ x := by
    have hs := (alAtomSynthesis_summable (alAtomCoordinates hAL x)).hasSum
    exact le_of_tendsto' hs (fun s => alAtomCoordinate_finite_sum_le hAL s x hx)
  have hz (a : NormalizedLatticeAtom E) : alAtomCoordinate hAL a (x-v) = 0 := by
    rw [map_sub]
    have hv := alAtomCoordinate_synthesis hAL a (alAtomCoordinates hAL x)
    change alAtomCoordinate hAL a v = alAtomCoordinate hAL a x at hv
    rw [hv, sub_self]
  change v = x
  by_contra hne
  have hres : x-v ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  obtain ⟨b, hb, hbr⟩ := hAtom (x-v) (sub_nonneg.mpr hvx) hres
  let a : NormalizedLatticeAtom E := hb.normalize
  have hbeq : b = ‖b‖ • (a : E) := by
    change b = ‖b‖ • (‖b‖⁻¹ • b)
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hb.2.1), one_smul]
  have hβb : alAtomCoordinate hAL a b = ‖b‖ := by
    calc
      alAtomCoordinate hAL a b = alAtomCoordinate hAL a (‖b‖ • (a : E)) :=
        congrArg (alAtomCoordinate hAL a) hbeq
      _ = ‖b‖ := by simp only [map_smul, alAtomCoordinate_self hAL, smul_eq_mul, mul_one]
  have hle := positive_operator_monotone (alAtomCoordinate_nonneg hAL a) hbr
  rw [hβb, hz a] at hle
  exact (norm_pos_iff.mpr hb.2.1).not_ge hle

theorem alAtomSynthesis_coordinates (x : E) : alAtomSynthesis (alAtomCoordinates hAL x) = x := by
  calc
    alAtomSynthesis (alAtomCoordinates hAL x) =
        alAtomSynthesis (alAtomCoordinates hAL (x⁺-x⁻)) := by rw [posPart_sub_negPart]
    _ = alAtomSynthesis (alAtomCoordinates hAL x⁺) -
        alAtomSynthesis (alAtomCoordinates hAL x⁻) := by rw [map_sub, map_sub]
    _ = x⁺-x⁻ := by rw [alAtomSynthesis_coordinates_of_nonneg hAL hAtom _ (posPart_nonneg x),
      alAtomSynthesis_coordinates_of_nonneg hAL hAtom _ (negPart_nonneg x)]
    _ = x := posPart_sub_negPart x

def alAtomicLinearEquiv : E ≃ₗ[ℝ] lp (fun _ : NormalizedLatticeAtom E => ℝ) 1 where
  toFun := alAtomCoordinates hAL
  invFun := alAtomSynthesis
  left_inv := alAtomSynthesis_coordinates hAL hAtom
  right_inv := alAtomCoordinates_synthesis hAL
  map_add' := map_add (alAtomCoordinates hAL)
  map_smul' := map_smul (alAtomCoordinates hAL)

def alAtomicIsometry : E ≃ₗᵢ[ℝ] lp (fun _ : NormalizedLatticeAtom E => ℝ) 1 :=
  { alAtomicLinearEquiv hAL hAtom with
    norm_map' := fun x => by
      apply le_antisymm (alAtomCoefficients_norm_le hAL x)
      have h := alAtomSynthesis_norm_le (alAtomCoordinates hAL x)
      rw [alAtomSynthesis_coordinates hAL hAtom] at h
      exact h }

def alAtomicEquiv : E ≃L[ℝ] lp (fun _ : NormalizedLatticeAtom E => ℝ) 1 :=
  (alAtomicIsometry hAL hAtom).toContinuousLinearEquiv

theorem alAtomicEquiv_nonneg_iff (x : E) :
    0 ≤ x ↔ ∀ a : NormalizedLatticeAtom E, 0 ≤ alAtomicEquiv hAL hAtom x a := by
  constructor
  · intro hx a
    exact alAtomCoordinate_nonneg hAL a x hx
  · intro hc
    rw [← alAtomSynthesis_coordinates hAL hAtom x, alAtomSynthesis_apply]
    exact tsum_nonneg (fun a => smul_nonneg (hc a) a.property.1.1)

/-- A complete atomic AL-lattice has an ordered ell-one representation with
the index type in the same universe as its carrier. -/
theorem exists_ordered_ellOne_of_atomic_AL :
    ∃ I : Type u, ∃ d : E ≃L[ℝ] lp (fun _ : I => ℝ) 1,
      ∀ x : E, 0 ≤ x ↔ ∀ i, 0 ≤ d x i :=
  ⟨NormalizedLatticeAtom E, alAtomicEquiv hAL hAtom, alAtomicEquiv_nonneg_iff hAL hAtom⟩

end ThesisCommon
