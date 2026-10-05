import ThesisCommon.Analysis.QuantitativeLpProducts
import ThesisCommon.Analysis.BoundedCZeroEquivalenceCalculus

/-! Exact sequence/product and head/tail identifications. The finite products
use the matching ℓp norm, so these maps have no norm conversion loss. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def isometryEquivOfNormBoundOne (e : X ≃L[𝕜] Y) (h : EquivNormBound e 1) : X ≃ₗᵢ[𝕜] Y :=
  ⟨e.toLinearEquiv, fun x => by
    apply le_antisymm
    · simpa only [one_mul] using h.1 x
    · simpa only [e.symm_apply_apply, one_mul] using h.2 (e x)⟩

theorem IsomorphicWithBound.sequenceSum {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C)
    (hC : 1 ≤ C) (p : BanachExponent) :
    IsomorphicWithBound 𝕜 (SequenceSum p X) (SequenceSum p Y) C := by
  obtain ⟨e, he⟩ := h.exists_sqrt_normBound hC
  have h' := (he.lpMap (Real.sqrt_nonneg C) p.val).isomorphicWithBound (Real.sqrt_nonneg C)
  simpa only [Real.sq_sqrt (zero_le_one.trans hC)] using h'

theorem IsomorphicWithBound.cZeroSum {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C)
    (hC : 1 ≤ C) : IsomorphicWithBound 𝕜 (CZeroSum X) (CZeroSum Y) C := by
  obtain ⟨e, he⟩ := h.exists_sqrt_normBound hC
  have h' := (he.cZeroMap (Real.sqrt_nonneg C)).isomorphicWithBound (Real.sqrt_nonneg C)
  simpa only [Real.sq_sqrt (zero_le_one.trans hC)] using h'

def sequenceProdEquiv (p : BanachExponent) :
    SequenceSum p (BanachDirectSum p X Y) ≃L[𝕜]
      BanachDirectSum p (SequenceSum p X) (SequenceSum p Y) :=
  ((lpMapEquiv (ι := ℕ) p.val (WithLp.prodContinuousLinearEquiv p.val 𝕜 X Y)).trans
    (lpProdEquiv p.val)).trans (WithLp.prodContinuousLinearEquiv p.val 𝕜 _ _).symm

theorem sequenceProdEquiv_norm (p : BanachExponent)
    (x : SequenceSum p (BanachDirectSum p X Y)) :
    ‖sequenceProdEquiv (𝕜 := 𝕜) p x‖ = ‖x‖ := by
  let y := sequenceProdEquiv (𝕜 := 𝕜) p x
  have hfst (i : ℕ) : y.fst i = (x i).fst := rfl
  have hsnd (i : ℕ) : y.snd i = (x i).snd := rfl
  by_cases hp : p.val = ∞
  · rcases p with ⟨p, hp'⟩
    change p = ∞ at hp
    subst p
    apply le_antisymm
    · change max ‖y.fst‖ ‖y.snd‖ ≤ ‖x‖
      apply max_le
      · apply lp.norm_le_of_forall_le (norm_nonneg x)
        intro i
        rw [hfst]
        exact (WithLp.norm_fst_le (α := X) (β := Y) (x i)).trans
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x i)
      · apply lp.norm_le_of_forall_le (norm_nonneg x)
        intro i
        rw [hsnd]
        exact (WithLp.norm_snd_le (α := X) (β := Y) (x i)).trans
          (lp.norm_apply_le_norm ENNReal.top_ne_zero x i)
    · apply lp.norm_le_of_forall_le (norm_nonneg y)
      intro i
      change max ‖(x i).fst‖ ‖(x i).snd‖ ≤ max ‖y.fst‖ ‖y.snd‖
      exact max_le_max
        (hfst i ▸ lp.norm_apply_le_norm ENNReal.top_ne_zero y.fst i)
        (hsnd i ▸ lp.norm_apply_le_norm ENNReal.top_ne_zero y.snd i)
  · have hp' : 0 < p.val.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le p.property)) hp
    have hpow (z : BanachDirectSum p X Y) :
        ‖z‖ ^ p.val.toReal = ‖z.fst‖ ^ p.val.toReal + ‖z.snd‖ ^ p.val.toReal := by
      rw [WithLp.prod_norm_eq_add hp', one_div, Real.rpow_inv_rpow (by positivity) hp'.ne']
    apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp'.ne').mp
    change ‖y‖ ^ p.val.toReal = ‖x‖ ^ p.val.toReal
    rw [WithLp.prod_norm_eq_add hp', one_div, Real.rpow_inv_rpow (by positivity) hp'.ne']
    rw [lp.norm_rpow_eq_tsum hp', lp.norm_rpow_eq_tsum hp', lp.norm_rpow_eq_tsum hp']
    rw [← ((lp.memℓp y.fst).summable hp').tsum_add ((lp.memℓp y.snd).summable hp')]
    apply tsum_congr
    intro i
    rw [hfst, hsnd, hpow]

def sequenceProdIsometry (p : BanachExponent) :
    SequenceSum p (BanachDirectSum p X Y) ≃ₗᵢ[𝕜]
      BanachDirectSum p (SequenceSum p X) (SequenceSum p Y) :=
  ⟨(sequenceProdEquiv p).toLinearEquiv, sequenceProdEquiv_norm p⟩

def sequenceHeadTailEquiv (p : BanachExponent) :
    SequenceSum p X ≃L[𝕜] BanachDirectSum p X (SequenceSum p X) :=
  (lpHeadTailEquiv p.val).trans (WithLp.prodContinuousLinearEquiv p.val 𝕜 _ _).symm

theorem sequenceHeadTailEquiv_norm (p : BanachExponent) (x : SequenceSum p X) :
    ‖sequenceHeadTailEquiv (𝕜 := 𝕜) p x‖ = ‖x‖ := by
  let y := sequenceHeadTailEquiv (𝕜 := 𝕜) p x
  have hfst : y.fst = x 0 := rfl
  have hsnd (i : ℕ) : y.snd i = x (i+1) := rfl
  by_cases hp : p.val = ∞
  · rcases p with ⟨p, hp'⟩
    change p = ∞ at hp
    subst p
    apply le_antisymm
    · change max ‖y.fst‖ ‖y.snd‖ ≤ ‖x‖
      apply max_le
      · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x 0
      · apply lp.norm_le_of_forall_le (norm_nonneg x)
        intro i
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero x (i+1)
    · apply lp.norm_le_of_forall_le (norm_nonneg y)
      intro i
      cases i with
      | zero => exact le_max_left _ _
      | succ i => exact (lp.norm_apply_le_norm ENNReal.top_ne_zero y.snd i).trans (le_max_right _ _)
  · have hp' : 0 < p.val.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le p.property)) hp
    apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp'.ne').mp
    change ‖y‖ ^ p.val.toReal = ‖x‖ ^ p.val.toReal
    rw [WithLp.prod_norm_eq_add hp', one_div, Real.rpow_inv_rpow (by positivity) hp'.ne']
    rw [lp.norm_rpow_eq_tsum hp', lp.norm_rpow_eq_tsum hp', hfst]
    change ‖x 0‖ ^ p.val.toReal + ∑' i, ‖x (i+1)‖ ^ p.val.toReal = _
    exact ((lp.memℓp x).summable hp').tsum_eq_zero_add.symm

def sequenceHeadTailIsometry (p : BanachExponent) :
    SequenceSum p X ≃ₗᵢ[𝕜] BanachDirectSum p X (SequenceSum p X) :=
  ⟨(sequenceHeadTailEquiv p).toLinearEquiv, sequenceHeadTailEquiv_norm p⟩

end ThesisCommon
