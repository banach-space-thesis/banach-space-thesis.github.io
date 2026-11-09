import BanachIsometric.ComplexHilbertInverseLimit

/-! The complex Theorem C equivalence, conditional on functional Theorem A
for the actual normed quotients. The forward tail theorem is in
`ComplexHilbertInverseLimit`: it keeps each specified seminorm and the original
complete Hausdorff uniformity, and supplies the canonical Hilbert inverse
limit. No normability conclusion is asserted. -/

noncomputable section
namespace BanachIsometric

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The normed separation model has exactly the paper's algebraic quotient
dimension. This displays the trigger using X/ker p literally. -/
theorem reducedNIsometric_iff_kernel_quotient_dimension
    (p : ℕ → Seminorm ℂ X) (n : ℕ) :
    ReducedNIsometric p n ↔
      ∀ k, (n : Cardinal) < Module.rank ℂ (X ⧸ seminormKernel (p k)) →
        MetricSubspaceHomogeneity ℂ (SeminormQuotient (p k)) n := by
  constructor
  · intro h k hk
    apply h k
    rw [← (seminormQuotientEquiv (p k)).rank_eq]
    exact hk
  · intro h k hk
    apply h k
    rw [(seminormQuotientEquiv (p k)).rank_eq]
    exact hk

theorem reducedNIsometric_of_hilbertian (p : ℕ → Seminorm ℂ X)
    (hp : ∀ k, SeminormIsHilbertian (p k)) (n : ℕ) : ReducedNIsometric p n := by
  intro k _
  exact complex_metricSubspaceHomogeneity_of_hasHermitianSquare
    (quotient_hasHermitianSquare_of_seminormIsHilbertian (p k) (hp k)) n

def AdmitsHilbertianGrading [UniformSpace X] : Prop :=
  ∃ p : ℕ → Seminorm ℂ X, Monotone p ∧ WithSeminorms p ∧
    ∀ k, SeminormIsHilbertian (p k)

def AdmitsReducedNIsometricGrading [UniformSpace X] (n : ℕ) : Prop :=
  ∃ p : ℕ → Seminorm ℂ X, Monotone p ∧ WithSeminorms p ∧ ReducedNIsometric p n

/-- The theorem's two existence assertions. Functional Theorem A is an
explicit dependency on normed quotients, not an added axiom or hidden premise
that a seminorm is already Hilbertian. -/
theorem admitsHilbertianGrading_iff_reducedNIsometricGrading_of_functional
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X] [T0Space X]
    (n : ℕ) (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hA : ∀ p : Seminorm ℂ X, ComplexFunctionalStatement (X := SeminormQuotient p)) :
    AdmitsHilbertianGrading (X := X) ↔ AdmitsReducedNIsometricGrading (X := X) n := by
  constructor
  · rintro ⟨p, hmono, hp, hHilb⟩
    exact ⟨p, hmono, hp, reducedNIsometric_of_hilbertian p hHilb n⟩
  · rintro ⟨p, hmono, hp, hReduced⟩
    obtain ⟨k₀, hTail, _⟩ := exists_cofinal_hilbert_inverseLimit p hmono hp n hn hdim
      (fun k => hA (p k)) hReduced
    exact ⟨(fun k => p (k + k₀)), seminormTail_monotone p hmono k₀,
      withSeminorms_tail p hmono hp k₀, fun k => (hTail k).1⟩

end BanachIsometric
