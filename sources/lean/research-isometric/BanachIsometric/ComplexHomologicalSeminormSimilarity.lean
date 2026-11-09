import BanachIsometric.ComplexSeminormSimilarityTorsion
import BanachIsometric.HomologicalFunctionalRigidity

/-! The original simultaneous scalar similarities force each nonzero seminorm to be Hermitian. -/
noncomputable section
namespace BanachIsometric
open Set Metric MeasureTheory
open scoped Quaternion Topology NNReal
variable {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem complex_seminorm_zero_or_hermitian_homological
    (p : Seminorm ℂ X) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hsim : ComplexSeminormSubspaceSimilarities p n) :
    (∀ x, p x = 0) ∨ HasHermitianSquare (p : X → ℝ) := by
  rcases complex_seminorm_zero_or_definite_of_similarities p n (by omega) hdim hsim with
    hzero | hdef
  · exact Or.inl hzero
  · right
    let M := MetricGeometry.DefiniteSeminormModel p hdef
    letI : NormedSpace ℂ M :=
      { inferInstanceAs (Module ℂ M) with
        norm_smul_le := fun a x => (norm_smul a x).le }
    let e : X ≃ₗ[ℂ] M := MetricGeometry.toDefiniteSeminormModel p hdef
    have hPair : SimultaneousPairSimilarities (𝕜 := ℂ) n (p : X → ℝ) p := by
      intro E F hE hF
      obtain ⟨T, c, hc, hT⟩ := hsim E F hE hF
      exact ⟨T, c, c, hc, hc, hT, hT⟩
    have hPairM := hPair.map e
    have hnorm : (fun y : M => p (e.symm y)) = norm := rfl
    rw [hnorm] at hPairM
    have hm : MetricSubspaceHomogeneity ℂ M n := by
      intro E F hE hF
      obtain ⟨T, c, _, hc, _, hT, _⟩ := hPairM E F
        (Module.finrank_eq_of_rank_eq hE) (Module.finrank_eq_of_rank_eq hF)
      exact ⟨(normalizedLinearSimilarity T c hc hT).toIsometryEquiv⟩
    have hHerm : HasHermitianSquare (norm : M → ℝ) :=
      complexTheoremA n norm hn
        (e.rank_eq.symm ▸ hdim) norm_isDefiniteComplexHomogeneous
        (norm_complexSphereLipschitz n) (metricSubspaceHomogeneity_realEquivalentSections hm)
    exact hHerm.pullback_injective e.toLinearMap e.injective

theorem complex_seminorm_pair_proportional_homological
    (p q : Seminorm ℂ X) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℂ X) (hpnonzero : ∃ x, p x ≠ 0)
    (hsim : SimultaneousPairSimilarities (𝕜 := ℂ) n (p : X → ℝ) q) :
    (∀ x, q x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, q x = a * p x := by
  have hpSim : ComplexSeminormSubspaceSimilarities p n := by
    intro E F hE hF
    obtain ⟨T, c, _, hc, _, hp, _⟩ := hsim E F hE hF
    exact ⟨T, c, hc, hp⟩
  have hqSim : ComplexSeminormSubspaceSimilarities q n := by
    intro E F hE hF
    obtain ⟨T, _, c, _, hc, _, hq⟩ := hsim E F hE hF
    exact ⟨T, c, hc, hq⟩
  have hpNotZero : ¬ ∀ x, p x = 0 := by
    obtain ⟨x, hx⟩ := hpnonzero
    exact fun hz => hx (hz x)
  have hpHerm := (complex_seminorm_zero_or_hermitian_homological
    p hn hdim hpSim).resolve_left hpNotZero
  have hpDef := (complex_seminorm_zero_or_definite_of_similarities p n (by omega)
    hdim hpSim).resolve_left hpNotZero
  rcases complex_seminorm_zero_or_hermitian_homological
    q hn hdim hqSim with hzero | hqHerm
  · exact Or.inl hzero
  · right
    let M := MetricGeometry.DefiniteSeminormModel p hpDef
    letI : NormedSpace ℂ M :=
      { inferInstanceAs (Module ℂ M) with
        norm_smul_le := fun a x => (norm_smul a x).le }
    let e : X ≃ₗ[ℂ] M := MetricGeometry.toDefiniteSeminormModel p hpDef
    have hpM : HasHermitianSquare (norm : M → ℝ) :=
      hpHerm.pullback_injective e.symm.toLinearMap e.symm.injective
    have hqM := hqHerm.pullback_injective e.symm.toLinearMap e.symm.injective
    have hsimM := hsim.map e
    have hnorm : (fun y : M => p (e.symm y)) = norm := rfl
    rw [hnorm] at hsimM
    obtain ⟨a, ha, hprop⟩ := complex_norm_proportional_of_hermitian_similarities hn
      (e.rank_eq.symm ▸ hdim) hpM hqM (fun y => apply_nonneg q (e.symm y)) hsimM
    exact ⟨a, ha, fun x => hprop (e x)⟩

theorem complexTheoremD
    {ι : Type*} (p : ι → Seminorm ℂ X) {n : ℕ} (hn : 2 ≤ n)
    (hdim : (n : Cardinal) < Module.rank ℂ X)
    (hseparating : ∀ x, (∀ i, p i x = 0) → x = 0)
    (hsim : ∀ E F : Submodule ℂ X,
      Module.finrank ℂ E = n → Module.finrank ℂ F = n →
      ∃ T : E ≃ₗ[ℂ] F, ∀ i, ∃ c : ℝ, 0 < c ∧
        ∀ x : E, p i (T x : X) = c * p i (x : X)) :
    ∃ i₀, HasHermitianSquare (p i₀ : X → ℝ) ∧
      ∀ i, (∀ x, p i x = 0) ∨ ∃ a : ℝ, 0 < a ∧ ∀ x, p i x = a * p i₀ x := by
  classical
  obtain ⟨x₀, hx₀⟩ := rank_pos_iff_exists_ne_zero.mp
    ((zero_le (n : Cardinal)).trans_lt hdim)
  have hex : ∃ i, p i x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx₀ (hseparating x₀ h)
  obtain ⟨i₀, hi₀⟩ := hex
  have hpair (i : ι) : SimultaneousPairSimilarities (𝕜 := ℂ) n (p i₀ : X → ℝ) (p i) := by
    intro E F hE hF
    obtain ⟨T, hT⟩ := hsim E F hE hF
    obtain ⟨c₀, hc₀, hp₀⟩ := hT i₀
    obtain ⟨c, hc, hp⟩ := hT i
    exact ⟨T, c₀, c, hc₀, hc, hp₀, hp⟩
  have hpSim : ComplexSeminormSubspaceSimilarities (p i₀) n := by
    intro E F hE hF
    obtain ⟨T, c, _, hc, _, hT, _⟩ := hpair i₀ E F hE hF
    exact ⟨T, c, hc, hT⟩
  have hNotZero : ¬ ∀ x, p i₀ x = 0 := fun hz => hi₀ (hz x₀)
  exact ⟨i₀, (complex_seminorm_zero_or_hermitian_homological
    (p i₀) hn hdim hpSim).resolve_left hNotZero,
    fun i => complex_seminorm_pair_proportional_homological
      (p i₀) (p i) hn hdim ⟨x₀, hi₀⟩ (hpair i)⟩

end BanachIsometric
