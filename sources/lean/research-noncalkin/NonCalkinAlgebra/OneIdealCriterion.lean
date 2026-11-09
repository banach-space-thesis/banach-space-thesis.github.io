import NonCalkinAlgebra.StatementLemmas
import Mathlib.Tactic.Push

noncomputable section
set_option autoImplicit false
namespace NonCalkinAlgebra
universe u
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

theorem twoSidedIdeal_smul_mem (I : TwoSidedIdeal A) {a : A} (ha : a ∈ I) (c : ℂ) :
    c • a ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left (algebraMap ℂ A c) a ha

/-- The algebraic last step of Proposition 5.1. The hypotheses are the
construction's scalar-plus-ideal decomposition, simplicity below the ideal,
and absence of an internal identity. All three remain explicit here.
-/
theorem one_ideal_of_scalar_extension (J : TwoSidedIdeal A)
    (hJ : IsNonzeroProperClosedIdeal J)
    (hspan : ∀ a : A, ∃ c : ℂ, ∃ j ∈ J, a = c • (1 : A) + j)
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I ≤ J → I = ⊥ ∨ I = J)
    (hnonunital : ¬ ∃ u ∈ J, ∀ b ∈ J, u * b = b ∧ b * u = b) :
    HasExactlyOneNonzeroProperClosedIdeal A := by
  apply (unique_closed_ideal_iff_three_ideals A).mpr
  refine ⟨J, hJ, ?_⟩
  intro L hL
  by_cases hzero : L = ⊥
  · exact Or.inl hzero
  have hinterClosed : IsClosed ((L ⊓ J : TwoSidedIdeal A) : Set A) := by
    change IsClosed ((L : Set A) ∩ (J : Set A))
    exact hL.inter hJ.1
  rcases hsimple (L ⊓ J) hinterClosed inf_le_right with hinter | hinter
  · have hexists : ∃ a : A, a ∈ L ∧ a ≠ 0 := by
      by_contra! h
      apply hzero
      apply le_antisymm _ bot_le
      intro a ha
      simpa only [TwoSidedIdeal.mem_bot] using h a ha
    obtain ⟨a, ha, hane⟩ := hexists
    obtain ⟨c, j, hj, heq⟩ := hspan a
    have hc : c ≠ 0 := by
      intro hc
      have haJ : a ∈ J := by simpa [heq, hc] using hj
      have hmem : a ∈ L ⊓ J := ⟨ha, haJ⟩
      rw [hinter, TwoSidedIdeal.mem_bot] at hmem
      exact hane hmem
    let v : A := c⁻¹ • j
    have hvJ : v ∈ J := twoSidedIdeal_smul_mem J hj c⁻¹
    have hvL : 1 + v ∈ L := by
      have h := twoSidedIdeal_smul_mem L ha c⁻¹
      simpa [heq, v, smul_add, smul_smul, inv_mul_cancel₀ hc] using h
    apply False.elim
    apply hnonunital
    refine ⟨-v, J.neg_mem hvJ, ?_⟩
    intro b hb
    have hleft : b + v * b = 0 := by
      have hmem : (1 + v) * b ∈ L ⊓ J :=
        ⟨L.mul_mem_right (1 + v) b hvL, J.mul_mem_left (1 + v) b hb⟩
      rw [hinter, TwoSidedIdeal.mem_bot] at hmem
      simpa only [add_mul, one_mul] using hmem
    have hright : b + b * v = 0 := by
      have hmem : b * (1 + v) ∈ L ⊓ J :=
        ⟨L.mul_mem_left b (1 + v) hvL, J.mul_mem_right b (1 + v) hb⟩
      rw [hinter, TwoSidedIdeal.mem_bot] at hmem
      simpa only [mul_add, mul_one] using hmem
    constructor
    · rw [neg_mul]
      exact (eq_neg_of_add_eq_zero_left hleft).symm
    · rw [mul_neg]
      exact (eq_neg_of_add_eq_zero_left hright).symm
  · have hJL : J ≤ L := by
      intro a ha
      have hmem : a ∈ L ⊓ J := by rw [hinter]; exact ha
      exact hmem.1
    by_cases hLJ : L ≤ J
    · exact Or.inr (Or.inl (le_antisymm hLJ hJL))
    · obtain ⟨a, ha, haJ⟩ := SetLike.not_le_iff_exists.mp hLJ
      obtain ⟨c, j, hj, heq⟩ := hspan a
      have hc : c ≠ 0 := by
        intro hc
        exact haJ (by simpa [heq, hc] using hj)
      have hscalar : c • (1 : A) ∈ L := by
        have h := L.sub_mem ha (hJL hj)
        simpa only [heq, add_sub_cancel_right] using h
      have hone : (1 : A) ∈ L := by
        have h := twoSidedIdeal_smul_mem L hscalar c⁻¹
        simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
      exact Or.inr (Or.inr (L.eq_top hone))

end NonCalkinAlgebra
