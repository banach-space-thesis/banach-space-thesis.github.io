import ThesisCommon.Analysis.ALFragmentBasic
import ThesisCommon.Analysis.FunctionalAtoms

/-! Normalized atoms and the norm functional of a real AL-lattice. These
are the indices and coordinate-functional ingredients of its atomic model. -/
noncomputable section
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

theorem IsPositiveLatticeAtom.smul_pos {a : E} (ha : IsPositiveLatticeAtom a)
    {r : ℝ} (hr : 0 < r) : IsPositiveLatticeAtom (r • a) := by
  refine ⟨smul_nonneg hr.le ha.1, smul_ne_zero hr.ne' ha.2.1, ?_⟩
  intro y hy hya
  have hinv : 0 ≤ r⁻¹ • y := smul_nonneg (inv_nonneg.mpr hr.le) hy
  have hinvle : r⁻¹ • y ≤ a := by
    have h := smul_le_smul_of_nonneg_left hya (inv_nonneg.mpr hr.le)
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
  obtain ⟨c, hc, he⟩ := ha.2.2 _ hinv hinvle
  refine ⟨c, hc, ?_⟩
  have h := congrArg (fun z : E => r • z) he
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, mul_comm r c] using h

theorem IsPositiveLatticeAtom.below_nsmul {a y : E} (ha : IsPositiveLatticeAtom a)
    (hy : 0 ≤ y) {n : ℕ} (hya : y ≤ n • a) : ∃ r : ℝ, 0 ≤ r ∧ y = r • a := by
  induction n generalizing y with
  | zero =>
    have hy0 : y = 0 := le_antisymm (by simpa using hya) hy
    exact ⟨0, le_rfl, by simp [hy0]⟩
  | succ n ih =>
    obtain ⟨u,v,hu,hua,hv,hva,huv⟩ := riesz_split_pair hy (nsmul_nonneg ha.1 n) ha.1
      (by simpa only [succ_nsmul] using hya)
    obtain ⟨r, hr, hu'⟩ := ih hu hua
    obtain ⟨s, hs, hv'⟩ := ha.2.2 _ hv hva
    exact ⟨r+s, add_nonneg hr hs, by rw [← huv, hu', hv', add_smul]⟩

abbrev NormalizedLatticeAtom (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] := {a : E // IsPositiveLatticeAtom a ∧ ‖a‖ = 1}

def IsPositiveLatticeAtom.normalize {a : E} (ha : IsPositiveLatticeAtom a) :
    NormalizedLatticeAtom E :=
  ⟨‖a‖⁻¹ • a, ha.smul_pos (inv_pos.mpr (norm_pos_iff.mpr ha.2.1)), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr ha.2.1))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha.2.1)⟩

theorem normalizedLatticeAtom_inf_eq_zero (a b : NormalizedLatticeAtom E) (hab : a ≠ b) :
    (a : E) ⊓ (b : E) = 0 := by
  have hc : 0 ≤ (a : E) ⊓ (b : E) := le_inf a.property.1.1 b.property.1.1
  obtain ⟨r, hr, hca⟩ := a.property.1.2.2 _ hc inf_le_left
  obtain ⟨s, hs, hcb⟩ := b.property.1.2.2 _ hc inf_le_right
  by_cases hr0 : r = 0
  · simpa only [hr0, zero_smul] using hca
  have hn : r = s := by
    have h := congrArg norm (hca.symm.trans hcb)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hs,
      a.property.2, b.property.2, mul_one] using h
  have he : r • (a : E) = r • (b : E) := by simpa only [← hn] using hca.symm.trans hcb
  have he' : (a : E) = (b : E) := by
    have h := congrArg (fun z : E => r⁻¹ • z) he
    simpa only [smul_smul, inv_mul_cancel₀ hr0, one_smul] using h
  exact (hab (Subtype.ext he')).elim

variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)

/-- The norm on positive vectors extends to a positive bounded functional. -/
def alNormFunctional : E →L[ℝ] ℝ :=
  positiveConeExtension (fun x _ => ‖x‖) hAL zero_le_one
    (fun x _ => by simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), one_mul]; exact le_rfl)

theorem alNormFunctional_apply_nonneg (x : E) (hx : 0 ≤ x) :
    alNormFunctional hAL x = ‖x‖ :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ x hx

theorem alNormFunctional_nonneg : 0 ≤ alNormFunctional hAL := by
  intro x hx
  change 0 ≤ alNormFunctional hAL x
  rw [alNormFunctional_apply_nonneg hAL x hx]
  exact norm_nonneg x

def alAtomCoordinate (a : NormalizedLatticeAtom E) : E →L[ℝ] ℝ :=
  functionalFragment (alNormFunctional hAL) (alNormFunctional_nonneg hAL) a

theorem alAtomCoordinate_nonneg (a : NormalizedLatticeAtom E) : 0 ≤ alAtomCoordinate hAL a :=
  functionalFragment_nonneg _ _ _

theorem alAtomCoordinate_self (a : NormalizedLatticeAtom E) : alAtomCoordinate hAL a a = 1 := by
  rw [alAtomCoordinate, functionalFragment_self _ _ _ a.property.1.1,
    alNormFunctional_apply_nonneg hAL _ a.property.1.1, a.property.2]

theorem alAtomCoordinate_other (a b : NormalizedLatticeAtom E) (hab : a ≠ b) :
    alAtomCoordinate hAL a b = 0 :=
  functionalFragment_disjoint _ _ a.property.1.1 b.property.1.1
    (normalizedLatticeAtom_inf_eq_zero a b hab)

end ThesisCommon
