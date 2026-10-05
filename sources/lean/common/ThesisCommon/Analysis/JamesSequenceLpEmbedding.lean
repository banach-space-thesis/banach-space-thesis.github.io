import ThesisCommon.Analysis.JamesSequenceSpaceComplete
import ThesisCommon.Analysis.LpOperators
import ThesisCommon.Analysis.LpCompactCoordinates

/-! Actual finite-p sequences map boundedly into James space. Finite increasing
paths use two injective coordinate samples, so their difference norms are at
most twice the lp norm. Inserting zeros at the odd coordinates gives the
embedding used in the complemented lp copy. -/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable (p : BanachExponent) (hp : p.val ≠ ∞)

include hp in
theorem finitePiLp_norm_rpow {n : ℕ} (v : PiLp p.val (fun _ : Fin n => 𝕜)) :
    ‖v‖ ^ p.val.toReal = ∑ j, ‖v j‖ ^ p.val.toReal := by
  have hpos := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  rw [PiLp.norm_eq_sum hpos,
    ← Real.rpow_mul (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)),
    one_div_mul_cancel hpos.ne', Real.rpow_one]

include hp in
theorem finiteLpSample_norm_le {n : ℕ} (e : Fin n ↪ ℕ)
    (a : SequenceSum p 𝕜) :
    ‖WithLp.toLp p.val (fun j => a (e j))‖ ≤ ‖a‖ := by
  classical
  have hpos := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hpos).mp
  rw [finitePiLp_norm_rpow p hp]
  have hs := lp.sum_rpow_le_norm_rpow hpos a (Finset.univ.image e)
  rwa [Finset.sum_image (fun _ _ _ _ h => e.injective h)] at hs

def finiteLpNullValue (a : SequenceSum p 𝕜) : CZeroSum 𝕜 where
  toFun := a
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (lp_norm_coordinates_tendsto_zero hp a)

def jamesPathLeftEmbedding (s : JamesPath) : Fin s.length ↪ ℕ where
  toFun j := s.index j.castSucc
  inj' := fun _ _ h => Fin.castSucc_injective s.length (s.strictMono.injective h)

def jamesPathRightEmbedding (s : JamesPath) : Fin s.length ↪ ℕ where
  toFun j := s.index j.succ
  inj' := fun _ _ h => Fin.succ_injective s.length (s.strictMono.injective h)

theorem jamesPath_finiteLp_norm_le (a : SequenceSum p 𝕜) (s : JamesPath) :
    ‖jamesPathMap 𝕜 p s (finiteLpNullValue p hp a)‖ ≤ 2 * ‖a‖ := by
  have heq : jamesPathMap 𝕜 p s (finiteLpNullValue p hp a) =
      WithLp.toLp p.val (fun j => a (jamesPathLeftEmbedding s j)) -
      WithLp.toLp p.val (fun j => a (jamesPathRightEmbedding s j)) := by
    ext j
    rfl
  rw [heq]
  exact (norm_sub_le _ _).trans (by
    have h := add_le_add (finiteLpSample_norm_le p hp (jamesPathLeftEmbedding s) a)
      (finiteLpSample_norm_le p hp (jamesPathRightEmbedding s) a)
    simpa only [two_mul] using h)

def lpToJamesValue (a : SequenceSum p 𝕜) : JamesSequenceSpace 𝕜 p :=
  ⟨finiteLpNullValue p hp a, ⟨2 * ‖a‖, by
    rintro _ ⟨s, rfl⟩
    exact jamesPath_finiteLp_norm_le p hp a s⟩⟩

theorem norm_lpToJamesValue_le (a : SequenceSum p 𝕜) :
    ‖lpToJamesValue p hp a‖ ≤ 2 * ‖a‖ :=
  JamesSequenceSpace.norm_le (jamesPath_finiteLp_norm_le p hp a)

def lpToJames : SequenceSum p 𝕜 →L[𝕜] JamesSequenceSpace 𝕜 p :=
  LinearMap.mkContinuous
    { toFun := lpToJamesValue p hp
      map_add' := by intros; ext n; rfl
      map_smul' := by intros; ext n; rfl }
    2 (norm_lpToJamesValue_le p hp)

@[simp] theorem lpToJames_apply (a : SequenceSum p 𝕜) (n : ℕ) :
    lpToJames (𝕜 := 𝕜) p hp a n = a n := rfl

theorem norm_lpToJames_le : ‖lpToJames (𝕜 := 𝕜) p hp‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

def jamesEvenEmbedding : ℕ ↪ ℕ where
  toFun n := 2 * n
  inj' := fun _ _ h => by dsimp at h; omega

/-- Insert the lp coefficients at the even positions and put zero at the odd positions. -/
def jamesLpInsert : SequenceSum p 𝕜 →L[𝕜] JamesSequenceSpace 𝕜 p :=
  (lpToJames p hp).comp (lpExtend p.val jamesEvenEmbedding)

@[simp] theorem jamesLpInsert_even (a : SequenceSum p 𝕜) (n : ℕ) :
    jamesLpInsert (𝕜 := 𝕜) p hp a (2 * n) = a n := by
  change lpExtend (𝕜 := 𝕜) p.val jamesEvenEmbedding a (jamesEvenEmbedding n) = a n
  exact lpExtend_apply_image jamesEvenEmbedding a n

@[simp] theorem jamesLpInsert_odd (a : SequenceSum p 𝕜) (n : ℕ) :
    jamesLpInsert (𝕜 := 𝕜) p hp a (2 * n + 1) = 0 := by
  change Function.extend jamesEvenEmbedding a 0 (2 * n + 1) = 0
  have h : ¬ ∃ k, jamesEvenEmbedding k = 2 * n + 1 := by
    rintro ⟨k, hk⟩
    change 2 * k = 2 * n + 1 at hk
    omega
  simp [Function.extend_apply' _ _ _ h]

theorem norm_jamesLpInsert_le : ‖jamesLpInsert (𝕜 := 𝕜) p hp‖ ≤ 2 := by
  apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
  have h := mul_le_mul (norm_lpToJames_le (𝕜 := 𝕜) p hp)
    (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) (p := p.val) jamesEvenEmbedding)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_one] using h

end ThesisCommon
