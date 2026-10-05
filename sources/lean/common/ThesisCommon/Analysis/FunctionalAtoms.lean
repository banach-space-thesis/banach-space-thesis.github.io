import ThesisCommon.Analysis.FunctionalFragmentPositive

/-! A positive atom in the actual continuous dual is a lattice homomorphism.
The proof constructs a dominated positive functional separating any pair of
disjoint positive vectors, then uses the one-dimensional order interval. -/
noncomputable section
namespace ThesisCommon
open scoped PositiveOperatorOrder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Lattice E] [IsOrderedAddMonoid E] [HasSolidNorm E]

def functionalFragment (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a : E) : E →L[ℝ] ℝ :=
  positiveConeExtension (fun x _ => functionalFragmentPos φ a x)
    (fun x y hx hy => functionalFragmentPos_add φ hφ a x y hx hy)
    (norm_nonneg φ) (fun x hx => functionalFragmentPos_norm_le φ hφ a x hx)

theorem functionalFragment_apply_nonneg (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a x : E) (hx : 0 ≤ x) :
    functionalFragment φ hφ a x = functionalFragmentPos φ a x :=
  positiveConeExtension_apply_of_nonneg _ _ _ _ x hx

theorem functionalFragment_nonneg (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a : E) :
    0 ≤ functionalFragment φ hφ a := by
  intro x hx
  change 0 ≤ functionalFragment φ hφ a x
  rw [functionalFragment_apply_nonneg φ hφ a x hx]
  exact functionalFragmentPos_nonneg φ hφ a x hx

theorem functionalFragment_le (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a : E) :
    functionalFragment φ hφ a ≤ φ := by
  intro x hx
  change functionalFragment φ hφ a x ≤ φ x
  rw [functionalFragment_apply_nonneg φ hφ a x hx]
  exact functionalFragmentPos_le φ hφ a x hx

theorem functionalFragment_self (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ) (a : E) (ha : 0 ≤ a) :
    functionalFragment φ hφ a a = φ a := by
  rw [functionalFragment_apply_nonneg φ hφ a a ha,functionalFragmentPos_self φ hφ a ha]

theorem functionalFragment_disjoint (φ : E →L[ℝ] ℝ) (hφ : 0 ≤ φ)
    {a x : E} (ha : 0 ≤ a) (hx : 0 ≤ x) (hax : a ⊓ x = 0) :
    functionalFragment φ hφ a x = 0 := by
  rw [functionalFragment_apply_nonneg φ hφ a x hx,functionalFragmentPos_disjoint φ hφ ha hx hax]

/-- A nonzero positive functional whose positive order interval is one dimensional. -/
def IsPositiveFunctionalAtom (φ : E →L[ℝ] ℝ) : Prop :=
  0 ≤ φ ∧ φ ≠ 0 ∧ ∀ ψ : E →L[ℝ] ℝ, 0 ≤ ψ → ψ ≤ φ → ∃ r : ℝ, 0 ≤ r ∧ ψ = r • φ

theorem IsPositiveFunctionalAtom.disjoint_values {φ : E →L[ℝ] ℝ} (hφ : IsPositiveFunctionalAtom φ)
    {a x : E} (ha : 0 ≤ a) (hx : 0 ≤ x) (hax : a ⊓ x = 0) : φ a = 0 ∨ φ x = 0 := by
  by_cases hzero : φ a = 0
  · exact Or.inl hzero
  right
  let ψ := functionalFragment φ hφ.1 a
  obtain ⟨r,_,hr⟩ := hφ.2.2 ψ (functionalFragment_nonneg φ hφ.1 a) (functionalFragment_le φ hφ.1 a)
  have ha' : 0 < φ a := lt_of_le_of_ne (hφ.1 a ha) (Ne.symm hzero)
  have heq : φ a = r * φ a := by
    have ht := congrArg (fun θ : E →L[ℝ] ℝ => θ a) hr
    change functionalFragment φ hφ.1 a a = r * φ a at ht
    rwa [functionalFragment_self φ hφ.1 a ha] at ht
  have hr1 : r = 1 := by nlinarith
  have hz := functionalFragment_disjoint φ hφ.1 ha hx hax
  change ψ x = 0 at hz
  simpa only [hr,hr1,one_smul] using hz

theorem IsPositiveFunctionalAtom.map_abs {φ : E →L[ℝ] ℝ} (hφ : IsPositiveFunctionalAtom φ) (x : E) :
    φ |x| = |φ x| := by
  have heq : φ x = φ x⁺ - φ x⁻ := by rw [← map_sub,posPart_sub_negPart]
  have hp : 0 ≤ φ x⁺ := hφ.1 _ (posPart_nonneg x)
  have hn : 0 ≤ φ x⁻ := hφ.1 _ (negPart_nonneg x)
  have hsum : φ |x| = φ x⁺ + φ x⁻ := by rw [← map_add,posPart_add_negPart]
  rcases hφ.disjoint_values (posPart_nonneg x) (negPart_nonneg x) (posPart_inf_negPart_eq_zero x) with h | h
  · rw [hsum,heq,h,zero_add,zero_sub,abs_neg,abs_of_nonneg hn]
  · rw [hsum,heq,h,add_zero,sub_zero,abs_of_nonneg hp]

end ThesisCommon
