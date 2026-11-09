import BanachIsometric.QuaternionicHilbertianQuotient
import BanachIsometric.QuaternionicFiniteIsometry

/-! The equivalence in quaternionic Theorem C, conditional precisely on the
functional theorem for the actual normed quotients. Both implications and the
substantive eventual Hilbertianity use the specified grading and right action. -/

namespace BanachIsometric.Quaternionic

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

theorem HermitianForm.seminorm_zero_iff_left_radical (h : HermitianForm X) (p : RightSeminorm X)
    (hdiag : ∀ x, h.form x x = (p x ^ 2 : ℝ)) (x : X) :
    p x = 0 ↔ ∀ y, h.form x y = 0 := by
  constructor
  · intro hx y
    exact h.eq_zero_of_seminorm_zero p hdiag x y hx
  · intro hx
    have hp2 : p x ^ 2 = 0 := by
      have hr := congrArg QuaternionAlgebra.re ((hdiag x).symm.trans (hx x))
      simpa only [Quaternion.re_coe, Quaternion.re_zero] using hr
    exact sq_eq_zero_iff.mp hp2

theorem reducedNIsometric_of_hilbertian (p : ℕ → RightSeminorm X)
    (hp : ∀ k, SeminormIsHilbertian (p k)) (n : ℕ) : ReducedNIsometric p n := by
  intro k _
  exact metricSubspaceHomogeneity_of_hasHermitianSquare
    (quotient_hasHermitianSquare_of_seminormIsHilbertian (p k) (hp k)) n

def AdmitsHilbertianGrading [UniformSpace X] : Prop :=
  ∃ p : ℕ → RightSeminorm X, Monotone (fun k => (p k).toRealSeminorm) ∧
    WithSeminorms (fun k => (p k).toRealSeminorm) ∧ ∀ k, SeminormIsHilbertian (p k)

def AdmitsReducedNIsometricGrading [UniformSpace X] (n : ℕ) : Prop :=
  ∃ p : ℕ → RightSeminorm X, Monotone (fun k => (p k).toRealSeminorm) ∧
    WithSeminorms (fun k => (p k).toRealSeminorm) ∧ ReducedNIsometric p n

theorem admitsHilbertianGrading_iff_reducedNIsometricGrading
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hA : ∀ p : RightSeminorm X, FunctionalStatement (E := SeminormQuotient p)) :
    AdmitsHilbertianGrading (X := X) ↔ AdmitsReducedNIsometricGrading (X := X) n := by
  constructor
  · rintro ⟨p, hmono, hp, hHilb⟩
    exact ⟨p, hmono, hp, reducedNIsometric_of_hilbertian p hHilb n⟩
  · rintro ⟨p, hmono, hp, hReduced⟩
    obtain ⟨k₀, hTail, _⟩ := exists_cofinal_hilbert_inverseLimit p hmono hp n hn hdim
      (fun k => hA (p k)) hReduced
    exact ⟨(fun k => p (k + k₀)), seminormTail_monotone p hmono k₀,
      withSeminorms_tail p hmono hp k₀, fun k => (hTail k).1⟩

end
end BanachIsometric.Quaternionic
