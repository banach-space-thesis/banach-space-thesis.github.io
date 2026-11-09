import CKEUPFP.DefinitionEquivalences
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.Real.Sqrt

/-!
# Balancing the two factors

Section 4 of the paper rescales pointwise factors with product norm at most C
so that both have norm at most √C. This module proves that step over both real
and complex scalars. The positive real rescaling is embedded using `RCLike`.
The trivial-space case is included separately, so no nonzero-space assumption
is added to the main result or to CPFP.
-/

noncomputable section

universe u v

namespace CKEUPFP

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a nonzero space, neither factor in a factorisation of the identity
can have zero norm. -/
theorem factor_norms_pos [Nontrivial E]
    (A L R : E →L[𝕜] E)
    (h : (L.comp A).comp R = ContinuousLinearMap.id 𝕜 E) :
    0 < ‖L‖ ∧ 0 < ‖R‖ := by
  constructor
  · apply norm_pos_iff.mpr
    intro hL
    have hn := congrArg (fun F : E →L[𝕜] E => ‖F‖) h
    simp [hL] at hn
  · apply norm_pos_iff.mpr
    intro hR
    have hn := congrArg (fun F : E →L[𝕜] E => ‖F‖) h
    simp [hR] at hn

/-- Rescaling genuine factors preserves their product and makes both
operator norms at most √C. The first new norm is exactly √C. -/
theorem exists_balanced_factors_of_product_bound [Nontrivial E]
    (A L R : E →L[𝕜] E) {C : ℝ} (hC : 1 ≤ C)
    (h : (L.comp A).comp R = ContinuousLinearMap.id 𝕜 E)
    (hbound : ‖L‖ * ‖R‖ ≤ C) :
    ∃ L' R' : E →L[𝕜] E,
      (L'.comp A).comp R' = ContinuousLinearMap.id 𝕜 E ∧
        ‖L'‖ ≤ Real.sqrt C ∧ ‖R'‖ ≤ Real.sqrt C := by
  have hc : 0 < C := zero_lt_one.trans_le hC
  have hsqrt : 0 < Real.sqrt C := Real.sqrt_pos.mpr hc
  have hLpos : 0 < ‖L‖ := (factor_norms_pos A L R h).1
  let a : ℝ := Real.sqrt C / ‖L‖
  have ha : 0 < a := div_pos hsqrt hLpos
  have hafield : (a : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr ha.ne'
  let L' : E →L[𝕜] E := (a : 𝕜) • L
  let R' : E →L[𝕜] E := ((a⁻¹ : ℝ) : 𝕜) • R
  refine ⟨L', R', ?_, ?_, ?_⟩
  · dsimp [L', R']
    simp only [ContinuousLinearMap.comp_smul,
      smul_smul, RCLike.ofReal_inv, mul_inv_cancel₀ hafield, one_smul, h]
  · change ‖(a : 𝕜) • L‖ ≤ Real.sqrt C
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ha]
    exact (div_mul_cancel₀ (Real.sqrt C) hLpos.ne').le
  · change ‖((a⁻¹ : ℝ) : 𝕜) • R‖ ≤ Real.sqrt C
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr ha)]
    calc
      a⁻¹ * ‖R‖ = (‖L‖ * ‖R‖) / Real.sqrt C := by
        dsimp [a]
        rw [inv_div, div_mul_eq_mul_div]
      _ ≤ C / Real.sqrt C := div_le_div_of_nonneg_right hbound hsqrt.le
      _ = Real.sqrt C := Real.div_sqrt

/-- The balanced-factor conclusion also holds on the zero space. -/
theorem FactorsThroughWith.exists_balanced_id_factors
    (A : E →L[𝕜] E) {C : ℝ} (hC : 1 ≤ C)
    (h : FactorsThroughWith (ContinuousLinearMap.id 𝕜 E) A C) :
    ∃ L R : E →L[𝕜] E,
      (L.comp A).comp R = ContinuousLinearMap.id 𝕜 E ∧
        ‖L‖ ≤ Real.sqrt C ∧ ‖R‖ ≤ Real.sqrt C := by
  rcases subsingleton_or_nontrivial E with htriv | hnontriv
  · letI : Subsingleton E := htriv
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro x
      exact Subsingleton.elim _ _
    · simpa only [norm_zero] using Real.sqrt_nonneg C
    · simpa only [norm_zero] using Real.sqrt_nonneg C
  · letI : Nontrivial E := hnontriv
    obtain ⟨L, R, hLR, hnorm⟩ := h
    exact exists_balanced_factors_of_product_bound A L R hC hLR hnorm

/-- CPFP gives its two alternatives with uniformly bounded individual factors,
as required for continuous selection in bounded strong operator balls. -/
theorem HasCPFP.exists_balanced_factorisation {C : ℝ}
    (h : HasCPFP 𝕜 E C) (A : E →L[𝕜] E) :
    (∃ L R : E →L[𝕜] E,
      (L.comp A).comp R = ContinuousLinearMap.id 𝕜 E ∧
        ‖L‖ ≤ Real.sqrt C ∧ ‖R‖ ≤ Real.sqrt C) ∨
    (∃ L R : E →L[𝕜] E,
      (L.comp (ContinuousLinearMap.id 𝕜 E - A)).comp R =
        ContinuousLinearMap.id 𝕜 E ∧
        ‖L‖ ≤ Real.sqrt C ∧ ‖R‖ ≤ Real.sqrt C) := by
  rcases h.2 A with hA | hA
  · exact Or.inl (hA.exists_balanced_id_factors A h.1)
  · exact Or.inr (hA.exists_balanced_id_factors _ h.1)

end CKEUPFP
