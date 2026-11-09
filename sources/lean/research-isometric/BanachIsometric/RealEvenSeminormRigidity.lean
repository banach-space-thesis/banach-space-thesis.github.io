import BanachIsometric.RealEvenNormRigidity
import BanachIsometric.RealOddSeminormTorsion

/-! The real even-section part of D. Original seminorms are proved quadratic,
and the same original real-linear similarities force their proportionality.
The generated topology and completeness then give the actual Hilbert model. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X]
theorem real_seminorm_zero_or_positiveGaugeData_of_even_similarities
    (p : Seminorm ℝ X) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hdim : (n : Cardinal) < Module.rank ℝ X) (hsim : RealSeminormSubspaceSimilarities p n) :
    (∀ x, p x = 0) ∨ Nonempty (MetricGeometry.PositiveGaugeData (p : X → ℝ)) := by
  rcases zero_or_definite_of_subspace_similarities p (MetricGeometry.seminormZeroSubmodule ℝ p)
    (fun _ => Iff.rfl) n (by omega) hdim hsim with hzero | hdef
  · exact Or.inl hzero
  · right
    let M := MetricGeometry.DefiniteSeminormModel p hdef
    letI : NormedSpace ℝ M :=
      { inferInstanceAs (Module ℝ M) with norm_smul_le := fun a x => (norm_smul a x).le }
    let e : X ≃ₗ[ℝ] M := MetricGeometry.toDefiniteSeminormModel p hdef
    have hPair : SimultaneousPairSimilarities (𝕜 := ℝ) n (p : X → ℝ) p := by
      intro E F hE hF
      obtain ⟨T, c, hc, hT⟩ := hsim E F hE hF
      exact ⟨T, c, c, hc, hc, hT, hT⟩
    have hPairM := hPair.map e
    have hnorm : (fun y : M => p (e.symm y)) = norm := rfl
    rw [hnorm] at hPairM
    have hm : MetricSubspaceHomogeneity ℝ M n := by
      intro E F hE hF
      obtain ⟨T, c, _, hc, _, hT, _⟩ := hPairM E F
        (Module.finrank_eq_of_rank_eq hE) (Module.finrank_eq_of_rank_eq hF)
      exact ⟨(normalizedLinearSimilarity T c hc hT).toIsometryEquiv⟩
    obtain ⟨D⟩ := real_even_norm_positiveGaugeData hn heven
      (e.rank_eq.symm ▸ hdim) hm
    exact ⟨D.comap e.toLinearMap e.injective⟩

theorem real_even_seminorm_pair_proportional
    (p q : Seminorm ℝ X) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hdim : (n : Cardinal) < Module.rank ℝ X) (hpnonzero : ∃ x, p x ≠ 0)
    (hsim : SimultaneousPairSimilarities (𝕜 := ℝ) n (p : X → ℝ) q) :
    (∀ x, q x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * p x := by
  have hpSim : RealSeminormSubspaceSimilarities p n := by
    intro E F hE hF
    obtain ⟨T, c, _, hc, _, hT, _⟩ := hsim E F hE hF
    exact ⟨T, c, hc, hT⟩
  have hqSim : RealSeminormSubspaceSimilarities q n := by
    intro E F hE hF
    obtain ⟨T, _, c, _, hc, _, hq⟩ := hsim E F hE hF
    exact ⟨T, c, hc, hq⟩
  have hpNotZero : ¬ ∀ x, p x = 0 := by obtain ⟨x, hx⟩ := hpnonzero; exact fun hz => hx (hz x)
  obtain ⟨Dp⟩ := (real_seminorm_zero_or_positiveGaugeData_of_even_similarities p hn heven hdim hpSim).resolve_left hpNotZero
  rcases real_seminorm_zero_or_positiveGaugeData_of_even_similarities q hn heven hdim hqSim with hzero | hqData
  · exact Or.inl hzero
  · obtain ⟨Dq⟩ := hqData
    exact Or.inr (positiveGaugeData_proportional_of_simultaneous_real_similarities Dp Dq (by omega) hdim hsim)

theorem real_even_separating_seminorm_family_collapse
    {ι : Type*} (p : ι → Seminorm ℝ X) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hseparating : ∀ x : X, x ≠ 0 → ∃ i, p i x ≠ 0)
    (hsim : ∀ E F : Submodule ℝ X, Module.finrank ℝ E = n → Module.finrank ℝ F = n →
      ∃ T : E ≃ₗ[ℝ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ _D : MetricGeometry.PositiveGaugeData (p i₀ : X → ℝ),
      ∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x := by
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp ((zero_le (n : Cardinal)).trans_lt hdim)
  obtain ⟨i₀, hi₀⟩ := hseparating x₀ hx₀
  have hpair (i : ι) : SimultaneousPairSimilarities (𝕜 := ℝ) n (p i₀ : X → ℝ) (p i) := by
    intro E F hE hF
    obtain ⟨T, hT⟩ := hsim E F hE hF
    obtain ⟨c₀, hc₀, hp₀⟩ := hT i₀
    obtain ⟨c, hc, hp⟩ := hT i
    exact ⟨T, c₀, c, hc₀, hc, hp₀, hp⟩
  have hSim₀ : RealSeminormSubspaceSimilarities (p i₀) n := by
    intro E F hE hF
    obtain ⟨T, c, _, hc, _, hT, _⟩ := hpair i₀ E F hE hF
    exact ⟨T, c, hc, hT⟩
  have hNotZero : ¬ ∀ x, p i₀ x = 0 := fun hz => hi₀ (hz x₀)
  obtain ⟨D⟩ := (real_seminorm_zero_or_positiveGaugeData_of_even_similarities (p i₀) hn heven hdim hSim₀).resolve_left hNotZero
  exact ⟨i₀, D, fun i => real_even_seminorm_pair_proportional
    (p i₀) (p i) hn heven hdim ⟨x₀, hi₀⟩ (hpair i)⟩

variable [UniformSpace X] [IsUniformAddGroup X]

theorem real_even_separating_seminorm_family_normable
    {ι : Type*} (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hseparating : ∀ x : X, x ≠ 0 → ∃ i, p i x ≠ 0)
    (hsim : ∀ E F : Submodule ℝ X, Module.finrank ℝ E = n → Module.finrank ℝ F = n →
      ∃ T : E ≃ₗ[ℝ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ D : MetricGeometry.PositiveGaugeData (p i₀ : X → ℝ),
      (∃ e : X ≃L[ℝ] MetricGeometry.GaugeNormModel D, ∀ x, ‖e x‖ = p i₀ x) ∧
      (∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x) ∧
      (CompleteSpace X → CompleteSpace (MetricGeometry.GaugeNormModel D)) := by
  obtain ⟨i₀, D, hcollapse⟩ := real_even_separating_seminorm_family_collapse
    p hn heven hdim hseparating hsim
  let e := MetricGeometry.toGaugeNormModel D
  have hnorm (x : X) : ‖e x‖ = p i₀ x := MetricGeometry.norm_gaugeNormModel D (e x)
  refine ⟨i₀, D, ⟨seminormFamilyNormContinuousLinearEquiv p hp i₀ e hnorm hcollapse, hnorm⟩, hcollapse, ?_⟩
  intro hcomplete
  letI : CompleteSpace X := hcomplete
  exact completeSpace_normModel_of_seminorm_family_collapse p hp i₀ e hnorm hcollapse

end
end BanachIsometric

