import BanachIsometric.ComplexHomologicalSeminormSimilarity
import BanachIsometric.HermitianGaugeModels
import BanachIsometric.SeminormFamilyNormTopology

/-! The actual uniformity and complete Hilbert model in the complex case of Theorem D. -/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal
open MetricGeometry

variable {ι X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
    [IsScalarTower ℝ ℂ X] [UniformSpace X] [IsUniformAddGroup X]

theorem complex_simultaneous_seminorms_norm_model_homological
    (p : ι → Seminorm ℂ X) (hp : WithSeminorms (fun i => (p i).restrictScalars ℝ))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hseparating : ∀ x, (∀ i, p i x = 0) → x = 0)
    (hsim : ∀ E F : Submodule ℂ X,
      Module.finrank ℂ E = n → Module.finrank ℂ F = n →
      ∃ T : E ≃ₗ[ℂ] F, ∀ i, ∃ c : ℝ, 0 < c ∧
        ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ D : PositiveGaugeData (p i₀ : X → ℝ),
      NormSMulClass ℂ (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      ∃ e : X ≃L[ℂ] GaugeNormModel D,
        (∀ x, ‖e x‖ = p i₀ x) ∧
        ∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x := by
  obtain ⟨i₀, ⟨h, hdiag⟩, hscale⟩ :=
    complexTheoremD p hn hdim
      hseparating hsim
  let D := complexPositiveGaugeData h hdiag (apply_nonneg (p i₀))
  have hnormsmul : NormSMulClass ℂ (GaugeNormModel D) :=
    gaugeNormModelNormSMul (R := ℂ) D (map_smul_eq_mul (p i₀))
  have hHerm : HasHermitianSquare (norm : GaugeNormModel D → ℝ) := by
    refine ⟨h, ?_⟩
    intro x
    rw [norm_gaugeNormModel]
    exact hdiag x
  let e : X ≃ₗ[ℂ] GaugeNormModel D := toGaugeNormModelScalar (R := ℂ) D
  have hnorm (x : X) : ‖e x‖ = p i₀ x := norm_gaugeNormModel D (e x)
  exact ⟨i₀, D, hnormsmul, hHerm,
    seminormFamilyNormContinuousLinearEquiv (fun i => (p i).restrictScalars ℝ)
      hp i₀ e hnorm hscale, hnorm, hscale⟩

theorem complex_simultaneous_seminorms_hilbert_model_homological
    [CompleteSpace X]
    (p : ι → Seminorm ℂ X) (hp : WithSeminorms (fun i => (p i).restrictScalars ℝ))
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hseparating : ∀ x, (∀ i, p i x = 0) → x = 0)
    (hsim : ∀ E F : Submodule ℂ X,
      Module.finrank ℂ E = n → Module.finrank ℂ F = n →
      ∃ T : E ≃ₗ[ℂ] F, ∀ i, ∃ c : ℝ, 0 < c ∧
        ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ D : PositiveGaugeData (p i₀ : X → ℝ),
      NormSMulClass ℂ (GaugeNormModel D) ∧ CompleteSpace (GaugeNormModel D) ∧
      HasHermitianSquare (norm : GaugeNormModel D → ℝ) ∧
      ∃ e : X ≃L[ℂ] GaugeNormModel D,
        (∀ x, ‖e x‖ = p i₀ x) ∧
        ∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x := by
  obtain ⟨i₀, D, hnormsmul, hHerm, e, hnorm, hscale⟩ :=
    complex_simultaneous_seminorms_norm_model_homological
      p hp hn hdim hseparating hsim
  exact ⟨i₀, D, hnormsmul,
    completeSpace_normModel_of_seminorm_family_collapse
      (fun i => (p i).restrictScalars ℝ) hp i₀ e.toLinearEquiv hnorm hscale,
    hHerm, e, hnorm, hscale⟩

end BanachIsometric
