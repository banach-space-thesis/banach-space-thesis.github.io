import ThesisCommon.Analysis.QuantitativeComplementedSplitting

/-! Exact rearrangements and distortion estimates for the genuine two-fold
ℓp norm. These preserve the constants used in Appendix A, for every p≥1,
including infinity and zero summands. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y Z A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]

theorem lpProductNorm_mono (r : BanachExponent)
    (x : BanachDirectSum r X Y) (y : BanachDirectSum r A B)
    (h₁ : ‖x.fst‖ ≤ ‖y.fst‖) (h₂ : ‖x.snd‖ ≤ ‖y.snd‖) : ‖x‖ ≤ ‖y‖ := by
  by_cases hr : r.val = ∞
  · rcases r with ⟨p, hp⟩
    change p = ∞ at hr
    subst p
    exact max_le_max h₁ h₂
  · have hp : 0 < r.val.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le r.property)) hr
    rw [WithLp.prod_norm_eq_add hp, WithLp.prod_norm_eq_add hp]
    gcongr

include 𝕜 in
omit [NormedSpace 𝕜 A] [NormedSpace 𝕜 B] in
theorem lpProductNorm_le_mul (r : BanachExponent)
    (x : BanachDirectSum r X Y) (y : BanachDirectSum r A B)
    {C : ℝ} (hC : 0 ≤ C)
    (h₁ : ‖y.fst‖ ≤ C * ‖x.fst‖) (h₂ : ‖y.snd‖ ≤ C * ‖x.snd‖) :
    ‖y‖ ≤ C * ‖x‖ := by
  have hn : ‖(C : 𝕜)‖ = C := by rw [RCLike.norm_ofReal, abs_of_nonneg hC]
  have h := lpProductNorm_mono r y ((C : 𝕜) • x)
    (by simpa only [WithLp.smul_fst, norm_smul, hn] using h₁)
    (by simpa only [WithLp.smul_snd, norm_smul, hn] using h₂)
  simpa only [norm_smul, hn] using h

def banachDirectSumCongr (r : BanachExponent) (e : X ≃L[𝕜] Y) (f : A ≃L[𝕜] B) :
    BanachDirectSum r X A ≃L[𝕜] BanachDirectSum r Y B :=
  ((WithLp.prodContinuousLinearEquiv r.val 𝕜 X A).trans (e.prodCongr f)).trans
    (WithLp.prodContinuousLinearEquiv r.val 𝕜 Y B).symm

theorem EquivNormBound.banachDirectSumCongr (r : BanachExponent)
    {e : X ≃L[𝕜] Y} {f : A ≃L[𝕜] B} {C : ℝ}
    (he : EquivNormBound e C) (hf : EquivNormBound f C) (hC : 0 ≤ C) :
    EquivNormBound (banachDirectSumCongr r e f) C := by
  constructor
  · intro x
    exact lpProductNorm_le_mul (𝕜 := 𝕜) r x _ hC (he.1 x.fst) (hf.1 x.snd)
  · intro y
    exact lpProductNorm_le_mul (𝕜 := 𝕜) r y _ hC (he.2 y.fst) (hf.2 y.snd)

theorem IsomorphicWithBound.banachDirectSumRight (r : BanachExponent)
    {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C) (hC : 1 ≤ C) :
    IsomorphicWithBound 𝕜 (BanachDirectSum r X Z) (BanachDirectSum r Y Z) C := by
  obtain ⟨e, he⟩ := h.exists_sqrt_normBound hC
  have hs : 1 ≤ Real.sqrt C := by nlinarith [Real.sq_sqrt (zero_le_one.trans hC), Real.sqrt_nonneg C]
  have h' := (he.banachDirectSumCongr r ((equivNormBound_refl (𝕜 := 𝕜) (X := Z)).mono hs)
    (Real.sqrt_nonneg C)).isomorphicWithBound (Real.sqrt_nonneg C)
  simpa only [Real.sq_sqrt (zero_le_one.trans hC)] using h'

theorem IsomorphicWithBound.banachDirectSumLeft (r : BanachExponent)
    {C : ℝ} (h : IsomorphicWithBound 𝕜 X Y C) (hC : 1 ≤ C) :
    IsomorphicWithBound 𝕜 (BanachDirectSum r Z X) (BanachDirectSum r Z Y) C := by
  obtain ⟨e, he⟩ := h.exists_sqrt_normBound hC
  have hs : 1 ≤ Real.sqrt C := by nlinarith [Real.sq_sqrt (zero_le_one.trans hC), Real.sqrt_nonneg C]
  have h' := (((equivNormBound_refl (𝕜 := 𝕜) (X := Z)).mono hs).banachDirectSumCongr r he
    (Real.sqrt_nonneg C)).isomorphicWithBound (Real.sqrt_nonneg C)
  simpa only [Real.sq_sqrt (zero_le_one.trans hC)] using h'

def banachDirectSumCommEquiv (r : BanachExponent) :
    BanachDirectSum r X Y ≃L[𝕜] BanachDirectSum r Y X :=
  ((WithLp.prodContinuousLinearEquiv r.val 𝕜 X Y).trans
    (ContinuousLinearEquiv.prodComm 𝕜 X Y)).trans
    (WithLp.prodContinuousLinearEquiv r.val 𝕜 Y X).symm

theorem banachDirectSumCommEquiv_norm (r : BanachExponent) (x : BanachDirectSum r X Y) :
    ‖banachDirectSumCommEquiv (𝕜 := 𝕜) r x‖ = ‖x‖ := by
  by_cases hr : r.val = ∞
  · rcases r with ⟨p, hp⟩
    change p = ∞ at hr
    subst p
    exact max_comm _ _
  · have hp : 0 < r.val.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le r.property)) hr
    rw [WithLp.prod_norm_eq_add hp, WithLp.prod_norm_eq_add hp]
    change (‖x.snd‖ ^ r.val.toReal + ‖x.fst‖ ^ r.val.toReal) ^ (1 / r.val.toReal) = _
    rw [add_comm]

def banachDirectSumComm (r : BanachExponent) :
    BanachDirectSum r X Y ≃ₗᵢ[𝕜] BanachDirectSum r Y X :=
  ⟨(banachDirectSumCommEquiv r).toLinearEquiv, banachDirectSumCommEquiv_norm r⟩

def banachDirectSumAssocEquiv (r : BanachExponent) :
    BanachDirectSum r (BanachDirectSum r X Y) Z ≃L[𝕜]
      BanachDirectSum r X (BanachDirectSum r Y Z) :=
  (WithLp.prodContinuousLinearEquiv r.val 𝕜 _ Z).trans
    (((WithLp.prodContinuousLinearEquiv r.val 𝕜 X Y).prodCongr
      (ContinuousLinearEquiv.refl 𝕜 Z)).trans
      ((ContinuousLinearEquiv.prodAssoc 𝕜 X Y Z).trans
        (((ContinuousLinearEquiv.refl 𝕜 X).prodCongr
          (WithLp.prodContinuousLinearEquiv r.val 𝕜 Y Z).symm).trans
          (WithLp.prodContinuousLinearEquiv r.val 𝕜 X _).symm)))

theorem banachDirectSumAssocEquiv_norm (r : BanachExponent)
    (x : BanachDirectSum r (BanachDirectSum r X Y) Z) :
    ‖banachDirectSumAssocEquiv (𝕜 := 𝕜) r x‖ = ‖x‖ := by
  by_cases hr : r.val = ∞
  · rcases r with ⟨p, hp⟩
    change p = ∞ at hr
    subst p
    exact (max_assoc _ _ _).symm
  · have hp : 0 < r.val.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le r.property)) hr
    change ‖WithLp.toLp r.val (x.fst.fst, WithLp.toLp r.val (x.fst.snd, x.snd))‖ = ‖x‖
    simp only [WithLp.prod_norm_eq_add hp]
    change (‖x.fst.fst‖ ^ r.val.toReal +
        ((‖x.fst.snd‖ ^ r.val.toReal + ‖x.snd‖ ^ r.val.toReal) ^
          (1 / r.val.toReal)) ^ r.val.toReal) ^ (1 / r.val.toReal) =
      (((‖x.fst.fst‖ ^ r.val.toReal + ‖x.fst.snd‖ ^ r.val.toReal) ^
          (1 / r.val.toReal)) ^ r.val.toReal + ‖x.snd‖ ^ r.val.toReal) ^ (1 / r.val.toReal)
    simp only [one_div]
    rw [Real.rpow_inv_rpow (by positivity) hp.ne', Real.rpow_inv_rpow (by positivity) hp.ne']
    rw [add_assoc]

def banachDirectSumAssoc (r : BanachExponent) :
    BanachDirectSum r (BanachDirectSum r X Y) Z ≃ₗᵢ[𝕜]
      BanachDirectSum r X (BanachDirectSum r Y Z) :=
  ⟨(banachDirectSumAssocEquiv r).toLinearEquiv, banachDirectSumAssocEquiv_norm r⟩

theorem isomorphicWithBound_of_isometry (e : X ≃ₗᵢ[𝕜] Y) :
    IsomorphicWithBound 𝕜 X Y 1 := by
  simpa only [one_pow] using (equivNormBound_isometry e).isomorphicWithBound zero_le_one

end ThesisCommon
