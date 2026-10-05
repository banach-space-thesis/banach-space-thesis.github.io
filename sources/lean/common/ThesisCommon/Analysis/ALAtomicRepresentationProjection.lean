import ThesisCommon.Analysis.ALAtomicRepresentationAtoms
import Mathlib.Topology.Order.Monotone

/-! The positive coordinate projection onto one normalized atom, and finite
coordinate sums bounded above by their positive input. -/
noncomputable section
open Set Finset
open scoped ThesisCommon.PositiveOperatorOrder
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]
variable (hAL : ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x+y‖ = ‖x‖+‖y‖)

theorem normalizedAtom_principal_eq (a : NormalizedLatticeAtom E)
    {y : E} (hy : 0 ≤ y) {n : ℕ} (hya : y ≤ n • (a : E)) : y = ‖y‖ • (a : E) := by
  obtain ⟨r, hr, rfl⟩ := a.property.1.below_nsmul hy hya
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, a.property.2, mul_one]

/-- The coefficient obtained from the principal functional fragment is
attained: its scalar multiple of the atom lies below the original vector. -/
theorem alAtomCoordinate_smul_le (a : NormalizedLatticeAtom E) (x : E) (hx : 0 ≤ x) :
    alAtomCoordinate hAL a x • (a : E) ≤ x := by
  let φ := alNormFunctional hAL
  have hφ := alNormFunctional_nonneg hAL
  have hne := functionalFragmentValues_nonempty φ a x hx
  have hb : BddAbove (functionalFragmentValues φ a x) :=
    ⟨functionalFragmentPos φ a x, (functionalFragmentPos_isLUB φ hφ a x hx).1⟩
  have hclosed : IsClosed {r : ℝ | r • (a : E) ≤ x} :=
    isClosed_le (continuous_id.smul continuous_const) continuous_const
  have hsub : functionalFragmentValues φ a x ⊆ {r : ℝ | r • (a : E) ≤ x} := by
    rintro _ ⟨y, hy, rfl⟩
    change φ y • (a : E) ≤ x
    obtain ⟨n, hn⟩ := hy.2.2
    have he : y = ‖y‖ • (a : E) := normalizedAtom_principal_eq a hy.1 hn
    change alNormFunctional hAL y • (a : E) ≤ x
    rw [alNormFunctional_apply_nonneg hAL y hy.1, ← he]
    exact hy.2.1
  have hmem := hclosed.closure_subset_iff.mpr hsub (csSup_mem_closure hne hb)
  change functionalFragmentPos φ a x • (a : E) ≤ x at hmem
  change functionalFragment φ hφ a x • (a : E) ≤ x
  rw [functionalFragment_apply_nonneg φ hφ a x hx]
  exact hmem

theorem alAtomCoordinate_sum (a : NormalizedLatticeAtom E)
    (s : Finset (NormalizedLatticeAtom E)) (c : NormalizedLatticeAtom E → ℝ) :
    alAtomCoordinate hAL a (∑ b ∈ s, c b • (b : E)) = if a ∈ s then c a else 0 := by
  classical
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  by_cases ha : a ∈ s
  · rw [if_pos ha]
    rw [sum_eq_single a]
    · rw [alAtomCoordinate_self hAL, mul_one]
    · intro b hb hba
      rw [alAtomCoordinate_other hAL a b (Ne.symm hba), mul_zero]
    · exact fun h => (h ha).elim
  · rw [if_neg ha]
    apply sum_eq_zero
    intro b hb
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    rw [alAtomCoordinate_other hAL a b hab, mul_zero]

theorem alAtomCoordinate_finite_sum_le (s : Finset (NormalizedLatticeAtom E))
    (x : E) (hx : 0 ≤ x) :
    (∑ a ∈ s, alAtomCoordinate hAL a x • (a : E)) ≤ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hx
  | @insert a s has ih =>
    let v := ∑ b ∈ s, alAtomCoordinate hAL b x • (b : E)
    have hres : 0 ≤ x-v := sub_nonneg.mpr ih
    have hcoord : alAtomCoordinate hAL a (x-v) = alAtomCoordinate hAL a x := by
      rw [map_sub]
      have hv := alAtomCoordinate_sum hAL a s (fun b => alAtomCoordinate hAL b x)
      rw [if_neg has] at hv
      change alAtomCoordinate hAL a x - alAtomCoordinate hAL a v = _
      rw [hv, sub_zero]
    have hbound := alAtomCoordinate_smul_le hAL a (x-v) hres
    rw [hcoord] at hbound
    rw [sum_insert has]
    exact add_le_of_le_sub_right hbound

theorem alAtomCoordinate_finite_sum_norm_le (s : Finset (NormalizedLatticeAtom E))
    (x : E) (hx : 0 ≤ x) : (∑ a ∈ s, alAtomCoordinate hAL a x) ≤ ‖x‖ := by
  have hpos (a : NormalizedLatticeAtom E) : 0 ≤ alAtomCoordinate hAL a x :=
    alAtomCoordinate_nonneg hAL a x hx
  have hterms (a : NormalizedLatticeAtom E) : 0 ≤ alAtomCoordinate hAL a x • (a : E) :=
    smul_nonneg (hpos a) a.property.1.1
  have heq : ‖∑ a ∈ s, alAtomCoordinate hAL a x • (a : E)‖ =
      ∑ a ∈ s, alAtomCoordinate hAL a x := by
    rw [al_norm_sum hAL s _ (fun a _ => hterms a)]
    apply sum_congr rfl
    intro a _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hpos a), a.property.2, mul_one]
  rw [← heq]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_of_nonneg (sum_nonneg fun a _ => hterms a), abs_of_nonneg hx]
  exact alAtomCoordinate_finite_sum_le hAL s x hx

end ThesisCommon
