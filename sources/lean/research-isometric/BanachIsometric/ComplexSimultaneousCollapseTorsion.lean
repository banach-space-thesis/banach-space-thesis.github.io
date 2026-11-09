import BanachIsometric.ComplexSeminormSimilarityTorsion
import BanachIsometric.HermitianGaugeModels
import BanachIsometric.SeminormFamilyNormTopology

/-! The full complex simultaneous-seminorm conclusion with the same explicit
remaining body-group even-homotopy torsion premise. A separating family
selects its nonzero anchor internally. The original family generates the
constructed Hermitian norm's actual uniformity, and completeness transfers
through that actual uniform equivalence. The original complex action is kept.
-/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal
open MetricGeometry

variable {ι X : Type*} [AddCommGroup X] [Module ℂ X] [Module ℝ X]
    [IsScalarTower ℝ ℂ X] [UniformSpace X] [IsUniformAddGroup X]

variable (hTorsion : ∀ (m : ℕ) (S : Set (EuclideanSpace ℝ (Fin m))),
  IsCompact S → closure (interior S) = S →
  (0 : EuclideanSpace ℝ (Fin m)) ∈ interior S →
  ∀ k : ℕ, Even (k + 2) →
  ∀ α : HomotopyGroup (Fin (k + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem complex_simultaneous_seminorms_norm_model_of_body_even_homotopy_torsion
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
    complex_seminorm_family_collapse_of_body_even_homotopy_torsion hTorsion p hn hdim
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

theorem complex_simultaneous_seminorms_hilbert_model_of_body_even_homotopy_torsion
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
    complex_simultaneous_seminorms_norm_model_of_body_even_homotopy_torsion
      hTorsion p hp hn hdim hseparating hsim
  exact ⟨i₀, D, hnormsmul,
    completeSpace_normModel_of_seminorm_family_collapse
      (fun i => (p i).restrictScalars ℝ) hp i₀ e.toLinearEquiv hnorm hscale,
    hHerm, e, hnorm, hscale⟩

end BanachIsometric
