import PosetsCommon.MaximalIdeals

/-! The algebraic criterion behind the maximal-ideal argument in Section 3:
if either x or 1-x factors the identity, nonfactorable elements form the
unique maximal ideal. For a Banach algebra this ideal is automatically closed. -/

noncomputable section
namespace ThesisCommon
variable {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

def IdentityNonfactorization (A : Type*) [Mul A] [One A] : Set A :=
  {x | ¬ ∃ a b : A, a * x * b = 1}

theorem identityNonfactorization_mul_left {x : A} (hx : x ∈ IdentityNonfactorization A)
    (y : A) : y * x ∈ IdentityNonfactorization A := by
  rintro ⟨a, b, h⟩
  exact hx ⟨a * y, b, by simpa only [mul_assoc] using h⟩

theorem identityNonfactorization_mul_right {x : A} (hx : x ∈ IdentityNonfactorization A)
    (y : A) : x * y ∈ IdentityNonfactorization A := by
  rintro ⟨a, b, h⟩
  exact hx ⟨a, y * b, by simpa only [mul_assoc] using h⟩

theorem proper_algebraIdeal_subset_identityNonfactorization {I : Set A}
    (hI : IsAlgebraIdeal 𝕜 I) (hp : I ≠ Set.univ) : I ⊆ IdentityNonfactorization A := by
  intro x hx
  rintro ⟨a, b, hab⟩
  have h1 : (1 : A) ∈ I := hab ▸ (hI.2.2.2 b (a * x) ((hI.2.2.2 a x hx).1)).2
  exact hp (hI.eq_univ_of_unit_mem h1 isUnit_one)

theorem identityNonfactorization_isAlgebraIdeal [Nontrivial A]
    (hsplit : ∀ x : A, (∃ a b : A, a * x * b = 1) ∨
      (∃ a b : A, a * (1 - x) * b = 1)) :
    IsAlgebraIdeal 𝕜 (IdentityNonfactorization A) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, h⟩
    exact zero_ne_one (by simpa only [mul_zero, zero_mul] using h)
  · intro x hx y hy
    rintro ⟨a, b, h⟩
    have hax := identityNonfactorization_mul_right (identityNonfactorization_mul_left hx a) b
    have hay := identityNonfactorization_mul_right (identityNonfactorization_mul_left hy a) b
    have he : 1 - a * x * b = a * y * b := by
      rw [sub_eq_iff_eq_add]
      simpa only [mul_add, add_mul, add_comm] using h.symm
    rcases hsplit (a * x * b) with h₁ | h₂
    · exact hax h₁
    · rw [he] at h₂
      exact hay h₂
  · intro c x hx
    rw [Algebra.smul_def]
    exact identityNonfactorization_mul_left hx (algebraMap 𝕜 A c)
  · intro a b hb
    exact ⟨identityNonfactorization_mul_left hb a, identityNonfactorization_mul_right hb a⟩

theorem identityNonfactorization_ne_univ : IdentityNonfactorization A ≠ Set.univ := by
  intro h
  have h1 : (1 : A) ∈ IdentityNonfactorization A := h.symm ▸ Set.mem_univ _
  exact h1 ⟨1, 1, by simp⟩

theorem identityNonfactorization_uniqueMaximal [Nontrivial A]
    (hsplit : ∀ x : A, (∃ a b : A, a * x * b = 1) ∨
      (∃ a b : A, a * (1 - x) * b = 1)) :
    ∃! I : Set A, IsMaximalAlgebraIdeal 𝕜 I := by
  have hI := identityNonfactorization_isAlgebraIdeal (𝕜 := 𝕜) hsplit
  have hp := identityNonfactorization_ne_univ (A := A)
  have hm : IsMaximalAlgebraIdeal 𝕜 (IdentityNonfactorization A) := by
    refine ⟨hI, hp, ?_⟩
    intro J hJ hIJ
    by_cases hJp : J = Set.univ
    · exact Or.inr hJp
    · exact Or.inl (Set.Subset.antisymm
        (proper_algebraIdeal_subset_identityNonfactorization hJ hJp) hIJ)
  refine ⟨IdentityNonfactorization A, hm, ?_⟩
  intro J hJ
  exact ((hJ.2.2 (IdentityNonfactorization A) hI
    (proper_algebraIdeal_subset_identityNonfactorization hJ.1 hJ.2.1)).resolve_right hp).symm

theorem identityNonfactorization_uniqueMaximalClosed [Nontrivial A] [CompleteSpace A]
    (hsplit : ∀ x : A, (∃ a b : A, a * x * b = 1) ∨
      (∃ a b : A, a * (1 - x) * b = 1)) :
    IsMaximalClosedIdeal 𝕜 (IdentityNonfactorization A) ∧ HasUniqueMaximalClosedIdeal 𝕜 A := by
  have h := identityNonfactorization_uniqueMaximal (𝕜 := 𝕜) hsplit
  have he : IsMaximalAlgebraIdeal 𝕜 (IdentityNonfactorization A) := by
    refine ⟨identityNonfactorization_isAlgebraIdeal hsplit, identityNonfactorization_ne_univ, ?_⟩
    intro J hJ hIJ
    by_cases hJp : J = Set.univ
    · exact Or.inr hJp
    · exact Or.inl (Set.Subset.antisymm
        (proper_algebraIdeal_subset_identityNonfactorization hJ hJp) hIJ)
  exact ⟨(isMaximalAlgebraIdeal_iff_isMaximalClosedIdeal _).mp he,
    uniqueMaximalAlgebraIdeal_iff_uniqueMaximalClosedIdeal.mp h⟩

end ThesisCommon
