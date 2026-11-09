import SurveyStatements.P1AlternatingRamsey
import SurveyStatements.P1ParityPadding
import SurveyStatements.P1RosenthalSmallScalarBlocks
import SurveyStatements.P1RosenthalPatternEstimate
import Mathlib.Tactic.FieldSimp

/-! The complex Rosenthal ℓ₁ dichotomy for actual bounded sequences.
The proof combines closed Ramsey selection with the finite complex
coefficient estimate and actual small scalar-sum blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem stable_scalar_obstruction_exists_arbitrary_patterns (s : ℕ → X)
    {ε M τ : ℝ} (hM : ∀ n, ‖s n‖ ≤ M) (hτ : 0 < τ)
    (hstable : ∀ κ : ℕ → ℕ, StrictMono κ → ¬ HasScalarTailDiameter (s ∘ κ) ε) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ F D : Finset ℕ, D ⊆ F →
        ∃ f : X →L[ℂ] ℂ, ∃ z w : ℂ, ‖f‖ ≤ 1 ∧ ‖z‖ ≤ M ∧ ε ≤ ‖w‖ ∧
          ∀ i ∈ F, ‖f (s (ρ i)) - (z + if i ∈ D then w else 0)‖ ≤ τ := by
  classical
  obtain ⟨μ, hμ, hpatterns⟩ :=
    stable_scalar_obstruction_exists_alternating_patterns s hM hτ hstable
  let sparse : ℕ → ℕ := fun n => 2 * n + 2
  have hsparse : StrictMono sparse := by
    intro i j hij
    dsimp [sparse]
    omega
  refine ⟨μ ∘ sparse, hμ.comp hsparse, ?_⟩
  intro F D hDF
  obtain ⟨G, hFG, hrank⟩ := exists_parity_padding F D hDF
  obtain ⟨f, z, w, hf, hz, hw, hpat⟩ := hpatterns G
  refine ⟨f, z, w, hf.le, hz, hw, ?_⟩
  intro i hi
  have hiG : sparse i ∈ G := hFG (Finset.mem_image_of_mem sparse hi)
  have h := hpat (sparse i) hiG
  dsimp only [sparse] at h
  rw [hrank i hi] at h
  by_cases hiD : i ∈ D
  · simpa [hiD, Function.comp_apply, sparse] using h
  · simpa [hiD, Function.comp_apply, sparse] using h

theorem complex_rosenthal_l1_or_weakCauchy (s : ℕ → X) {M : ℝ}
    (hM : ∀ n, ‖s n‖ ≤ M) :
    (∃ ν : ℕ → ℕ, StrictMono ν ∧ ∃ L : ℝ, 0 < L ∧
      (∀ b : ℕ →₀ ℂ, L * coefficientL1Mass b ≤
        ‖Finsupp.linearCombination ℂ (s ∘ ν) b‖) ∧
      (∀ b : ℕ →₀ ℂ, ‖Finsupp.linearCombination ℂ (s ∘ ν) b‖ ≤
        M * coefficientL1Mass b)) ∨
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ IsWeakCauchySequence (s ∘ ν) := by
  classical
  by_cases hL1 : ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∃ L : ℝ, 0 < L ∧
      ∀ b : ℕ →₀ ℂ, L * coefficientL1Mass b ≤
        ‖Finsupp.linearCombination ℂ (s ∘ ν) b‖
  · obtain ⟨ν, hν, L, hL, hlower⟩ := hL1
    exact Or.inl ⟨ν, hν, L, hL, hlower,
      fun b => bounded_sequence_upper_l1_estimate (s ∘ ν) (fun n => hM (ν n)) b⟩
  · right
    by_contra hno
    obtain ⟨ε, hε, ν, hν, hstable⟩ :=
      no_weakCauchy_subsequence_exists_stable_scalar_obstruction s hno
    have hMnonneg : 0 ≤ M := (norm_nonneg (s 0)).trans (hM 0)
    have hMone : 0 < 1 + M := by linarith
    let τ : ℝ := ε / (16 * (1 + M))
    have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) hMone)
    have hτeq : (1 + M) * τ = ε / 16 := by
      dsimp [τ]
      field_simp [hMone.ne']
      <;> ring
    obtain ⟨ρ, hρ, hpatterns⟩ :=
      stable_scalar_obstruction_exists_arbitrary_patterns (s ∘ ν)
        (fun n => hM (ν n)) hτ hstable
    let e : ℕ → X := s ∘ ν ∘ ρ
    have hnoLower (κ : ℕ → ℕ) (hκ : StrictMono κ) :
        ¬ ∃ L : ℝ, 0 < L ∧ ∀ b : ℕ →₀ ℂ,
          L * coefficientL1Mass b ≤ ‖Finsupp.linearCombination ℂ (e ∘ κ) b‖ := by
      intro h
      exact hL1 ⟨ν ∘ ρ ∘ κ, hν.comp (hρ.comp hκ), h⟩
    obtain ⟨b, hb, hnorm, hsum⟩ :=
      no_lower_l1_subsequence_exists_small_scalar_block e hnoLower
        (ε := ε / 8) (by positivity) hτ
    have hbmass : (∑ i ∈ b.support, ‖b i‖) = 1 := hb
    have hbscalar : ‖∑ i ∈ b.support, b i‖ ≤ τ := by
      simpa only [coefficientScalarSum, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, mul_one] using hsum.le
    have hfinite : ‖∑ i ∈ b.support, b i • e i‖ ≤ ε / 8 := hnorm
    have hbound := exists_complex_pattern_coefficient_estimate b.support b e hτ.le
      hbmass hbscalar (hpatterns b.support)
    rw [hτeq] at hbound
    linarith

end SurveyStatements.P1
