import BanachIsometric.ComplexHilbertianQuotient
import BanachIsometric.ComplexHilbertNorm

/-! The forward direction of complex Theorem C, conditional precisely on
functional Theorem A on the actual normed quotients. Eventual quotient
dimension, Hermitian seminorms, Hilbert completions, and the canonical inverse
limit all refer to the specified original grading and uniformity. -/

noncomputable section
namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- Exactly the dimension trigger in the paper: only quotients whose complex
dimension exceeds n are required to have metric-isometric n-sections. -/
def ReducedNIsometric (p : ℕ → Seminorm ℂ X) (n : ℕ) : Prop :=
  ∀ k, (n : Cardinal) < Module.rank ℂ (SeminormQuotient (p k)) →
    MetricSubspaceHomogeneity ℂ (SeminormQuotient (p k)) n

theorem reduced_quotient_hasHermitianSquare_of_functional
    (p : ℕ → Seminorm ℂ X) (n : ℕ) (hn : 2 ≤ n)
    (hA : ∀ k, ComplexFunctionalStatement (X := SeminormQuotient (p k)))
    (hReduced : ReducedNIsometric p n) (k : ℕ)
    (hdim : (n : Cardinal) < Module.rank ℂ (SeminormQuotient (p k))) :
    HasHermitianSquare (norm : SeminormQuotient (p k) → ℝ) :=
  hA k n norm hn hdim norm_isDefiniteComplexHomogeneous (norm_complexSphereLipschitz n)
    (metricSubspaceHomogeneity_realEquivalentSections (hReduced k hdim))

theorem exists_cofinal_hilbert_inverseLimit
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (p : ℕ → Seminorm ℂ X) (hmono : Monotone p) (hp : WithSeminorms p)
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hA : ∀ k, ComplexFunctionalStatement (X := SeminormQuotient (p k)))
    (hReduced : ReducedNIsometric p n) :
    ∃ k₀ : ℕ, (∀ k, SeminormIsHilbertian (p (k + k₀)) ∧
      ComplexIsHilbertForNorm (V := SeminormCompletion (p (k + k₀)))) ∧
      Nonempty (X ≃L[ℂ] seminormLimitSubmodule (fun k => p (k + k₀))
        (seminormTail_monotone p hmono k₀)) := by
  obtain ⟨k₀, hk₀⟩ := cofinal_seminorm_quotient_dimension p hmono hp n hdim
  refine ⟨k₀, ?_, ⟨seminormTailInverseLimitEquiv p hmono hp k₀⟩⟩
  intro k
  have hdimk := hk₀ (k + k₀) (by omega)
  have hSquare := reduced_quotient_hasHermitianSquare_of_functional p n hn hA hReduced
    (k + k₀) hdimk
  exact ⟨seminormIsHilbertian_of_quotient_square _ hSquare,
    complex_completion_isHilbertForNorm hSquare⟩

/-- The literal canonical bonding map on every cofinal tail has dense range.
It is the already-constructed contraction between these actual completions. -/
theorem completedSeminormTailFactor_denseRange (p : ℕ → Seminorm ℂ X)
    (hmono : Monotone p) (k₀ k : ℕ) :
    DenseRange (completedSeminormFactor
      ((seminormTail_monotone p hmono k₀) (Nat.le_succ k))) :=
  completedSeminormFactor_denseRange _

end BanachIsometric
