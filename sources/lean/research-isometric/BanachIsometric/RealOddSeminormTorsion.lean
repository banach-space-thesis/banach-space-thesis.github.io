import BanachIsometric.RealOddNormRigidity
import BanachIsometric.PositiveGaugePullback
import BanachIsometric.DefiniteSeminormModel
import BanachIsometric.MetricGaugeIsometries
import BanachIsometric.SeminormFamilyNormTopology
import BanachIsometric.HermitianGlobalProportionality
import BanachIsometric.SimilarityKernel

/-! The real ODD-section part of D: actual seminorms become quadratic and
collapse under the same original real-linear similarities. The generated
uniformity and completeness are consequences. No real even-section Banach
or Gromov theorem, initial Hermitianity or proportionality is assumed. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

def RealSeminormSubspaceSimilarities (p : Seminorm ℝ X) (n : ℕ) : Prop :=
  ∀ E F : Submodule ℝ X, Module.finrank ℝ E = n → Module.finrank ℝ F = n →
    ∃ T : E ≃ₗ[ℝ] F, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p (T x : X) = c * p (x : X)

theorem positiveGaugeData_proportional_of_simultaneous_real_similarities
    {p q : X → ℝ} (Dp : MetricGeometry.PositiveGaugeData p) (Dq : MetricGeometry.PositiveGaugeData q)
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hsim : SimultaneousPairSimilarities (𝕜 := ℝ) n p q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * p x := by
  let e := MetricGeometry.toGaugeNormModel Dp
  let B : MetricGeometry.GaugeNormModel Dp →ₗ[ℝ] MetricGeometry.GaugeNormModel Dp →ₗ[ℝ] ℝ :=
    Dq.bilinear.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hB : ∀ x y, star (B x y) = B y x := fun x y => Dq.symmetric (e.symm x) (e.symm y)
  have hpos : ∀ x : MetricGeometry.GaugeNormModel Dp, x ≠ 0 → 0 < B x x := by
    intro x hx
    change 0 < Dq.bilinear (e.symm x) (e.symm x)
    rw [Dq.diagonal]
    exact sq_pos_of_ne_zero ((Dq.eq_zero_iff _).not.mpr
      (fun hz => hx (e.symm.injective (hz.trans e.symm.map_zero.symm))))
  have hsimM := hsim.map e
  have hnorm : (fun y : MetricGeometry.GaugeNormModel Dp => p (e.symm y)) = norm := by
    funext y
    exact (MetricGeometry.norm_gaugeNormModel Dp y).symm
  rw [hnorm] at hsimM
  obtain ⟨a, ha, hprop⟩ := hermitianNorm_global_proportional_of_simultaneous_similarities (𝕜 := ℝ)
    hn (e.rank_eq.symm ▸ hdim) B hB hpos (fun y => q (e.symm y))
    (fun y => Dq.nonneg (e.symm y)) (fun y => Dq.diagonal (e.symm y)) hsimM
  refine ⟨a, ha, ?_⟩
  intro x
  have h := hprop (e x)
  rw [e.symm_apply_apply, MetricGeometry.norm_gaugeNormModel] at h
  exact h

variable (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
  ∀ j : ℕ, Even (j + 2) →
  ∀ α : HomotopyGroup (Fin (j + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem real_seminorm_zero_or_positiveGaugeData_of_odd_similarities
    (p : Seminorm ℝ X) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
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
    obtain ⟨D⟩ := real_odd_norm_positiveGaugeData_of_body_even_homotopy_torsion hTorsion hn hodd
      (e.rank_eq.symm ▸ hdim) hm
    exact ⟨D.comap e.toLinearMap e.injective⟩

theorem real_odd_seminorm_pair_proportional_of_body_even_homotopy_torsion
    (p q : Seminorm ℝ X) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
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
  obtain ⟨Dp⟩ := (real_seminorm_zero_or_positiveGaugeData_of_odd_similarities hTorsion p hn hodd hdim hpSim).resolve_left hpNotZero
  rcases real_seminorm_zero_or_positiveGaugeData_of_odd_similarities hTorsion q hn hodd hdim hqSim with hzero | hqData
  · exact Or.inl hzero
  · obtain ⟨Dq⟩ := hqData
    exact Or.inr (positiveGaugeData_proportional_of_simultaneous_real_similarities Dp Dq (by omega) hdim hsim)

theorem real_odd_separating_seminorm_family_collapse_of_body_even_homotopy_torsion
    {ι : Type*} (p : ι → Seminorm ℝ X) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
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
  obtain ⟨D⟩ := (real_seminorm_zero_or_positiveGaugeData_of_odd_similarities hTorsion (p i₀) hn hodd hdim hSim₀).resolve_left hNotZero
  exact ⟨i₀, D, fun i => real_odd_seminorm_pair_proportional_of_body_even_homotopy_torsion
    hTorsion (p i₀) (p i) hn hodd hdim ⟨x₀, hi₀⟩ (hpair i)⟩

variable [UniformSpace X] [IsUniformAddGroup X]

theorem real_odd_separating_seminorm_family_normable_of_body_even_homotopy_torsion
    {ι : Type*} (p : ι → Seminorm ℝ X) (hp : WithSeminorms p) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hdim : (n : Cardinal) < Module.rank ℝ X)
    (hseparating : ∀ x : X, x ≠ 0 → ∃ i, p i x ≠ 0)
    (hsim : ∀ E F : Submodule ℝ X, Module.finrank ℝ E = n → Module.finrank ℝ F = n →
      ∃ T : E ≃ₗ[ℝ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀ : ι, ∃ D : MetricGeometry.PositiveGaugeData (p i₀ : X → ℝ),
      (∃ e : X ≃L[ℝ] MetricGeometry.GaugeNormModel D, ∀ x, ‖e x‖ = p i₀ x) ∧
      (∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x) ∧
      (CompleteSpace X → CompleteSpace (MetricGeometry.GaugeNormModel D)) := by
  obtain ⟨i₀, D, hcollapse⟩ := real_odd_separating_seminorm_family_collapse_of_body_even_homotopy_torsion
    hTorsion p hn hodd hdim hseparating hsim
  let e := MetricGeometry.toGaugeNormModel D
  have hnorm (x : X) : ‖e x‖ = p i₀ x := MetricGeometry.norm_gaugeNormModel D (e x)
  refine ⟨i₀, D, ⟨seminormFamilyNormContinuousLinearEquiv p hp i₀ e hnorm hcollapse, hnorm⟩, hcollapse, ?_⟩
  intro hcomplete
  letI : CompleteSpace X := hcomplete
  exact completeSpace_normModel_of_seminorm_family_collapse p hp i₀ e hnorm hcollapse

end
end BanachIsometric

