import BanachIsometric.QuaternionicSeminormSimilarityTorsion
import BanachIsometric.HomologicalFunctionalRigidity

/-! The original simultaneous scalar similarities force each nonzero seminorm to be Hermitian. -/
noncomputable section
namespace BanachIsometric.Quaternionic
open Set Metric MeasureTheory
open scoped Quaternion Topology NNReal
variable {X : Type*} [AddCommGroup X] [Module Hᵐᵒᵖ X] [Module ℝ X]

theorem rightSeminorm_zero_or_hermitian_homological (p : RightSeminorm X)
    {n : ℕ} (hn : 2 ≤ n) (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hsim : SeminormSubspaceSimilarities p n) :
    (∀ x, p x = 0) ∨ HasHermitianSquare (p : X → ℝ) := by
  rcases rightSeminorm_zero_or_definite_of_similarities p n (by omega) hdim hsim with hzero | hdef
  · exact Or.inl hzero
  · right
    let pK := p.oppositeSeminorm
    let M := MetricGeometry.DefiniteSeminormModel pK hdef
    let e : X ≃ₗ[Hᵐᵒᵖ] M := MetricGeometry.toDefiniteSeminormModel pK hdef
    have hPair : SimultaneousPairSimilarities (𝕜 := Hᵐᵒᵖ) n (p : X → ℝ) p := by
      intro E F hE hF
      obtain ⟨T, c, hc, hT⟩ := hsim E F hE hF
      exact ⟨T, c, c, hc, hc, hT, hT⟩
    have hPairM := hPair.map e
    have hnorm : (fun y : M => p (e.symm y)) = norm := rfl
    rw [hnorm] at hPairM
    have hReal : RealEquivalentSections n (norm : M → ℝ) :=
      norm_realEquivalentSections_of_scalar_similarities (fun E F hE hF => by
        obtain ⟨T, c, _, hc, _, hT, _⟩ := hPairM E F hE hF
        exact ⟨T, c, hc, hT⟩)
    have hHp : HasHermitianSquare (norm : M → ℝ) :=
      theoremA n norm hn
        (e.rank_eq.symm ▸ hdim) norm_isDefiniteHomogeneous (norm_sphereLipschitz n) hReal
    exact hHp.pullback_injective e.toLinearMap e.injective

theorem rightSeminorm_pair_proportional_homological
    (p q : RightSeminorm X) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X)
    (hpnonzero : ∃ x, p x ≠ 0)
    (hsim : SimultaneousPairSimilarities (𝕜 := Hᵐᵒᵖ) n (p : X → ℝ) q) :
    (∀ x, q x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * p x := by
  have hpSim : SeminormSubspaceSimilarities p n := by
    intro E F hE hF
    obtain ⟨T, c, _, hc, _, hp, _⟩ := hsim E F hE hF
    exact ⟨T, c, hc, hp⟩
  have hqSim : SeminormSubspaceSimilarities q n := by
    intro E F hE hF
    obtain ⟨T, _, c, _, hc, _, hq⟩ := hsim E F hE hF
    exact ⟨T, c, hc, hq⟩
  have hpNotZero : ¬ ∀ x, p x = 0 := by obtain ⟨x, hx⟩ := hpnonzero; exact fun hz => hx (hz x)
  have hpHerm := (rightSeminorm_zero_or_hermitian_homological
    p hn hdim hpSim).resolve_left hpNotZero
  have hpDef := (rightSeminorm_zero_or_definite_of_similarities p n (by omega) hdim hpSim).resolve_left hpNotZero
  rcases rightSeminorm_zero_or_hermitian_homological q hn hdim hqSim with hzero | hqHerm
  · exact Or.inl hzero
  · right
    let pK := p.oppositeSeminorm
    let M := MetricGeometry.DefiniteSeminormModel pK hpDef
    let e : X ≃ₗ[Hᵐᵒᵖ] M := MetricGeometry.toDefiniteSeminormModel pK hpDef
    have hpM : HasHermitianSquare (norm : M → ℝ) := hpHerm.pullback_injective e.symm.toLinearMap e.symm.injective
    have hqM := hqHerm.pullback_injective e.symm.toLinearMap e.symm.injective
    have hsimM := hsim.map e
    have hnorm : (fun y : M => p (e.symm y)) = norm := rfl
    rw [hnorm] at hsimM
    obtain ⟨a, ha, hprop⟩ := quaternionic_norm_proportional_of_hermitian_similarities hn
      (e.rank_eq.symm ▸ hdim) hpM hqM (fun y => apply_nonneg q.toRealSeminorm (e.symm y)) hsimM
    refine ⟨a, ha, ?_⟩
    intro x
    exact hprop (e x)

theorem rightSeminorm_family_collapse_homological
    {ι : Type*} (p : ι → RightSeminorm X) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank Hᵐᵒᵖ X) (i₀ : ι) (hpnonzero : ∃ x, p i₀ x ≠ 0)
    (hsim : ∀ E F : Submodule Hᵐᵒᵖ X,
      Module.finrank Hᵐᵒᵖ E = n → Module.finrank Hᵐᵒᵖ F = n →
      ∃ T : E ≃ₗ[Hᵐᵒᵖ] F, ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    HasHermitianSquare (p i₀ : X → ℝ) ∧
      ∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x := by
  have hpair (i : ι) : SimultaneousPairSimilarities (𝕜 := Hᵐᵒᵖ) n (p i₀ : X → ℝ) (p i) := by
    intro E F hE hF
    obtain ⟨T, hT⟩ := hsim E F hE hF
    obtain ⟨c₀, hc₀, hp₀⟩ := hT i₀
    obtain ⟨c, hc, hp⟩ := hT i
    exact ⟨T, c₀, c, hc₀, hc, hp₀, hp⟩
  have hSim₀ : SeminormSubspaceSimilarities (p i₀) n := by
    intro E F hE hF
    obtain ⟨T, c, _, hc, _, hT, _⟩ := hpair i₀ E F hE hF
    exact ⟨T, c, hc, hT⟩
  have hNotZero : ¬ ∀ x, p i₀ x = 0 := by obtain ⟨x, hx⟩ := hpnonzero; exact fun hz => hx (hz x)
  exact ⟨(rightSeminorm_zero_or_hermitian_homological (p i₀) hn hdim hSim₀).resolve_left hNotZero,
    fun i => rightSeminorm_pair_proportional_homological (p i₀) (p i) hn hdim hpnonzero (hpair i)⟩

end BanachIsometric.Quaternionic
end
