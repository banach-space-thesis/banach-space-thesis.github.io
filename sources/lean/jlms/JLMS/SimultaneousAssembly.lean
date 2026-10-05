import JLMS.Simultaneous
import JLMS.Rescaling

/-!
# Section 8: from individual factorizations to minimality

For positive summable weights ρₙ, the threshold 2/ρₙ² in the essential norm
produces factor maps with norms below ρₙ. Summing them along an orthogonal
c₀ block system proves the minimality assertion. With ρₙ = 2⁻ⁿ the threshold
is precisely the paper's 2^(2n+1), with indexing beginning at zero.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The individual factorization conclusion of Theorem 1.6, on a fixed space. -/
def FactorTwoFactorizations (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∀ T : E →L[𝕜] E, ¬ IsCompactOperator T → ∀ ε : ℝ, 0 < ε →
    ∃ U : E →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] E,
      (U.comp T).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ * ‖V‖ < 2 / essentialNorm T + ε

/-- The rescaled maps in Lemma 8.2 are summable in norm. -/
theorem exists_summable_factor_maps (hfactor : FactorTwoFactorizations 𝕜 E)
    (ρ : ℕ → ℝ) (hρ : ∀ j, 0 < ρ j) (hsum : Summable ρ)
    (T : ℕ → E →L[𝕜] E) (hT : ∀ j, 2 / (ρ j) ^ 2 < essentialNorm (T j)) :
    ∃ U : ℕ → E →L[𝕜] cZero 𝕜, ∃ V : ℕ → cZero 𝕜 →L[𝕜] E,
      (∀ j, ((U j).comp (T j)).comp (V j) = ContinuousLinearMap.id 𝕜 (cZero 𝕜)) ∧
      (Summable fun j => ‖U j‖) ∧ (Summable fun j => ‖V j‖) := by
  have hsmall (j : ℕ) : ∃ U : E →L[𝕜] cZero 𝕜, ∃ V : cZero 𝕜 →L[𝕜] E,
      (U.comp (T j)).comp V = ContinuousLinearMap.id 𝕜 (cZero 𝕜) ∧
      ‖U‖ < ρ j ∧ ‖V‖ < ρ j := by
    have hr2 : 0 < (ρ j) ^ 2 := sq_pos_of_pos (hρ j)
    have he : 0 < essentialNorm (T j) := (div_pos (by norm_num) hr2).trans (hT j)
    have hnc : ¬ IsCompactOperator (T j) := by
      intro hc
      have hz := (essentialNorm_eq_zero_iff (T j)).mpr hc
      linarith
    have hgap : 2 / essentialNorm (T j) < (ρ j) ^ 2 := by
      have hlarge := (div_lt_iff₀ hr2).mp (hT j)
      apply (div_lt_iff₀ he).mpr
      nlinarith
    let ε := ((ρ j) ^ 2 - 2 / essentialNorm (T j)) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨U, V, hUV, hnorm⟩ := hfactor (T j) hnc ε hε
    have hprod : ‖U‖ * ‖V‖ < (ρ j) ^ 2 := by dsimp [ε] at hnorm; linarith
    exact exists_small_factor_maps (T j) U V hUV (hρ j) hprod
  choose U V hUV hU hV using hsmall
  refine ⟨U, V, hUV, ?_, ?_⟩
  · exact hsum.of_nonneg_of_le (fun j => norm_nonneg (U j)) (fun j => (hU j).le)
  · exact hsum.of_nonneg_of_le (fun j => norm_nonneg (V j)) (fun j => (hV j).le)

/-- Lemma 8.2's simultaneous factorization property, for a supplied c₀ block
system. Neither summability nor the common factor maps remain assumptions. -/
theorem simultaneousFactorizations_of_factor_two
    (R : OrthogonalRetracts 𝕜 E (cZero 𝕜)) (hfactor : FactorTwoFactorizations 𝕜 E)
    (ρ : ℕ → ℝ) (hρ : ∀ j, 0 < ρ j) (hsum : Summable ρ) :
    SimultaneousFactorizations R.block (fun j => 2 / (ρ j) ^ 2) := by
  intro T hT
  obtain ⟨U, V, hUV, hU, hV⟩ := exists_summable_factor_maps hfactor ρ hρ hsum T hT
  exact R.exists_simultaneous_of_summable T U V hUV hU hV

/-- The full Section 8 minimality argument, with only the c₀ block system and
the preceding individual factorization theorem left as external inputs. -/
theorem essentialNormIsMinimal_of_factor_two
    (R : OrthogonalRetracts 𝕜 E (cZero 𝕜)) (hfactor : FactorTwoFactorizations 𝕜 E) :
    EssentialNormIsMinimal 𝕜 E := by
  let ρ : ℕ → ℝ := fun j => (1 / 2) ^ j
  have hρ : ∀ j, 0 < ρ j := fun j => pow_pos (by norm_num) j
  have hsum : Summable ρ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hZ : ¬ IsCompactOperator (ContinuousLinearMap.id 𝕜 (cZero 𝕜)) := by
    intro h
    exact cZero_not_finiteDimensional 𝕜 (finiteDimensional_of_compact_identity h)
  apply essentialNormIsMinimal_of_simultaneous R.block (fun j => 2 / (ρ j) ^ 2)
    (fun j => div_pos (by norm_num) (sq_pos_of_pos (hρ j))) R.block_idempotent
    (R.block_noncompact hZ)
  exact simultaneousFactorizations_of_factor_two R hfactor ρ hρ hsum

end JLMS
