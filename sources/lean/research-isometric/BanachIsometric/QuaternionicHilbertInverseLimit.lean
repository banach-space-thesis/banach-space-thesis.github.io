import BanachIsometric.QuaternionicSeminormTail
import BanachIsometric.QuaternionicCorollaryCompletion

/-! The honest conditional Hilbertian conclusion for the actual quaternionic
seminorm inverse system. Functional Theorem A and the metric hypotheses on
the actual quotients remain explicit; the cofinal dimensions, completions,
Hilbert norm forms and inverse-limit equivalence are consequences. -/

namespace BanachIsometric.Quaternionic

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]

/-- Exactly the paper's reduced n-isometry hypothesis: homogeneity is required
only at levels whose actual quaternionic quotient dimension exceeds n. -/
def ReducedNIsometric (p : ℕ → RightSeminorm X) (n : ℕ) : Prop :=
  ∀ k, (n : Cardinal) < Module.rank Hᵐᵒᵖ (SeminormQuotient (p k)) →
    MetricSubspaceHomogeneity (V := SeminormQuotient (p k)) n

/-- A positive-semidefinite quaternionic Hermitian square inducing the actual
seminorm. Its diagonal is nonnegative because it equals the real square p². -/
def SeminormIsHilbertian (p : RightSeminorm X) : Prop :=
  ∃ h : HermitianForm X, ∀ x, h.form x x = (p x ^ 2 : ℝ)

omit [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X] in
theorem seminormIsHilbertian_of_quotient_square (p : RightSeminorm X)
    (hp : HasHermitianSquare (norm : SeminormQuotient p → ℝ)) : SeminormIsHilbertian p := by
  obtain ⟨h, hdiag, _⟩ := hp
  refine ⟨h.comap (seminormQuotientMap p), ?_⟩
  intro x
  change h.form (seminormQuotientMap p x) (seminormQuotientMap p x) = _
  simpa only [seminormQuotientMap_norm] using hdiag (seminormQuotientMap p x)

theorem exists_cofinal_hilbert_inverseLimit (p : ℕ → RightSeminorm X)
    (hmono : Monotone (fun i => (p i).toRealSeminorm))
    (hp : WithSeminorms (fun i => (p i).toRealSeminorm))
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hA : ∀ k, FunctionalStatement (E := SeminormQuotient (p k)))
    (hmetric : ReducedNIsometric p n) :
    ∃ k₀ : ℕ, (∀ k, SeminormIsHilbertian (p (k + k₀)) ∧
      IsHilbertForNorm (V := SeminormCompletion (p (k + k₀)))) ∧
      Nonempty (X ≃L[Hᵐᵒᵖ] seminormLimitSubmodule (fun k => p (k + k₀)) (seminormTail_monotone p hmono k₀)) := by
  obtain ⟨k₀, hk₀⟩ := cofinal_seminorm_quotient_dimension p hmono hp n hdim
  refine ⟨k₀, ?_, ⟨seminormTailInverseLimitEquiv p hmono hp k₀⟩⟩
  intro k
  have hdimk := hk₀ (k + k₀) (by omega)
  have hSquare : HasHermitianSquare (norm : SeminormQuotient (p (k + k₀)) → ℝ) :=
    (functionalStatement_implies_corollaryB (hA (k + k₀)) n) hn hdimk (hmetric (k + k₀) hdimk)
  exact ⟨seminormIsHilbertian_of_quotient_square _ hSquare, completion_isHilbertForNorm hSquare⟩

end
end BanachIsometric.Quaternionic
