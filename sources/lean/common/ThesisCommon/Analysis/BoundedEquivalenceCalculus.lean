import ThesisCommon.Analysis.SequenceSumEquivs
import ThesisCommon.Analysis.UniformPrimariness

/-! Elementary estimates on actual bounded equivalences. The common
two-sided bound is a proved norm estimate on a supplied map, not an assumed
existence of any decomposition. Products use their actual maximum norm. -/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 X Y Z A B : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]

def EquivNormBound (e : X ≃L[𝕜] Y) (C : ℝ) : Prop :=
  (∀ x, ‖e x‖ ≤ C * ‖x‖) ∧ ∀ y, ‖e.symm y‖ ≤ C * ‖y‖

theorem EquivNormBound.symm {e : X ≃L[𝕜] Y} {C : ℝ}
    (h : EquivNormBound e C) : EquivNormBound e.symm C := ⟨h.2, h.1⟩

theorem EquivNormBound.mono {e : X ≃L[𝕜] Y} {C D : ℝ}
    (h : EquivNormBound e C) (hCD : C ≤ D) : EquivNormBound e D :=
  ⟨fun x => (h.1 x).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg x)),
    fun y => (h.2 y).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg y))⟩

theorem EquivNormBound.trans {e : X ≃L[𝕜] Y} {f : Y ≃L[𝕜] Z} {C D : ℝ}
    (h : EquivNormBound e C) (hf : EquivNormBound f D) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    EquivNormBound (e.trans f) (C * D) := by
  constructor
  · intro x
    exact (hf.1 (e x)).trans (by nlinarith [h.1 x])
  · intro z
    exact (h.2 (f.symm z)).trans (by nlinarith [hf.2 z])

theorem EquivNormBound.prodCongr {e : X ≃L[𝕜] Y} {f : A ≃L[𝕜] B} {C : ℝ}
    (h : EquivNormBound e C) (hf : EquivNormBound f C) (hC : 0 ≤ C) :
    EquivNormBound (e.prodCongr f) C := by
  constructor
  · intro x
    apply max_le
    · exact (h.1 x.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le x) hC)
    · exact (hf.1 x.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le x) hC)
  · intro y
    apply max_le
    · exact (h.2 y.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le y) hC)
    · exact (hf.2 y.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le y) hC)

theorem equivNormBound_refl : EquivNormBound (ContinuousLinearEquiv.refl 𝕜 X) 1 := by
  constructor <;> intro x <;> simp [one_mul]

theorem equivNormBound_comm : EquivNormBound (ContinuousLinearEquiv.prodComm 𝕜 X Y) 1 := by
  constructor <;> intro x <;> simp [Prod.norm_def, max_comm]

theorem equivNormBound_assoc : EquivNormBound (ContinuousLinearEquiv.prodAssoc 𝕜 X Y Z) 1 := by
  constructor
  · intro x
    change max ‖x.1.1‖ (max ‖x.1.2‖ ‖x.2‖) ≤ 1 * max (max ‖x.1.1‖ ‖x.1.2‖) ‖x.2‖
    rw [one_mul, max_assoc]
  · intro x
    change max (max ‖x.1‖ ‖x.2.1‖) ‖x.2.2‖ ≤ 1 * max ‖x.1‖ (max ‖x.2.1‖ ‖x.2.2‖)
    rw [one_mul, max_assoc]

theorem equivNormBound_isometry (e : X ≃ₗᵢ[𝕜] Y) :
    EquivNormBound e.toContinuousLinearEquiv 1 := by
  constructor <;> intro x <;> simp

theorem EquivNormBound.isomorphicWithBound {e : X ≃L[𝕜] Y} {C : ℝ}
    (h : EquivNormBound e C) (hC : 0 ≤ C) : IsomorphicWithBound 𝕜 X Y (C ^ 2) := by
  refine ⟨e, ?_⟩
  have h₁ := ContinuousLinearMap.opNorm_le_bound e.toContinuousLinearMap hC h.1
  have h₂ := ContinuousLinearMap.opNorm_le_bound e.symm.toContinuousLinearMap hC h.2
  simpa only [pow_two] using mul_le_mul h₁ h₂ (norm_nonneg _) hC

theorem EquivNormBound.lpMap {e : X ≃L[𝕜] Y} {C : ℝ}
    (h : EquivNormBound e C) (hC : 0 ≤ C) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    EquivNormBound (lpMapEquiv (ι := ℕ) p e) C := by
  constructor
  · intro x
    apply lp_norm_le_mul_of_pointwise x _ hC
    intro i
    exact h.1 (x i)
  · intro x
    apply lp_norm_le_mul_of_pointwise x _ hC
    intro i
    exact h.2 (x i)

theorem equivNormBound_lpProd (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    EquivNormBound (lpProdEquiv (𝕜 := 𝕜) (ι := ℕ) (X := X) (Y := Y) p) 2 := by
  constructor
  · intro x
    apply max_le
    · have h : ‖lpMap p (ContinuousLinearMap.fst 𝕜 X Y) x‖ ≤ 1 * ‖x‖ :=
        lp_norm_le_mul_of_pointwise x _ zero_le_one (fun i => by simpa using norm_fst_le (x i))
      change ‖lpMap p (ContinuousLinearMap.fst 𝕜 X Y) x‖ ≤ 2 * ‖x‖
      nlinarith [norm_nonneg x]
    · have h : ‖lpMap p (ContinuousLinearMap.snd 𝕜 X Y) x‖ ≤ 1 * ‖x‖ :=
        lp_norm_le_mul_of_pointwise x _ zero_le_one (fun i => by simpa using norm_snd_le (x i))
      change ‖lpMap p (ContinuousLinearMap.snd 𝕜 X Y) x‖ ≤ 2 * ‖x‖
      nlinarith [norm_nonneg x]
  · intro x
    have h₁ : ‖lpMap p (ContinuousLinearMap.inl 𝕜 X Y) x.1‖ ≤ 1 * ‖x.1‖ :=
      lp_norm_le_mul_of_pointwise x.1 _ zero_le_one (fun i => by simp)
    have h₂ : ‖lpMap p (ContinuousLinearMap.inr 𝕜 X Y) x.2‖ ≤ 1 * ‖x.2‖ :=
      lp_norm_le_mul_of_pointwise x.2 _ zero_le_one (fun i => by simp)
    change ‖lpMap p (ContinuousLinearMap.inl 𝕜 X Y) x.1 +
      lpMap p (ContinuousLinearMap.inr 𝕜 X Y) x.2‖ ≤ 2 * ‖x‖
    exact (norm_add_le _ _).trans (by nlinarith [norm_fst_le x, norm_snd_le x])

theorem equivNormBound_lpHeadTail (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    EquivNormBound (lpHeadTailEquiv (𝕜 := 𝕜) (X := X) p) 2 := by
  constructor
  · intro x
    apply max_le
    · have h := lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) x 0
      change ‖x 0‖ ≤ 2 * ‖x‖
      nlinarith [norm_nonneg x]
    · have h := (lpRestrict (𝕜 := 𝕜) (X := X) p sequenceSuccessor).le_of_opNorm_le
        (norm_lpRestrict_le (𝕜 := 𝕜) (X := X) (p := p) sequenceSuccessor) x
      change ‖lpRestrict (𝕜 := 𝕜) p sequenceSuccessor x‖ ≤ 2 * ‖x‖
      nlinarith [norm_nonneg x]
  · intro x
    have h₁ : ‖lp.single (E := fun _ : ℕ => X) p 0 x.1‖ ≤ ‖x.1‖ :=
      (lp.norm_single (E := fun _ : ℕ => X) (p := p)
        (zero_lt_one.trans_le (Fact.out : 1 ≤ p)) 0 x.1).le
    have h₂ : ‖lpExtend (𝕜 := 𝕜) p sequenceSuccessor x.2‖ ≤ ‖x.2‖ := by
      have h := (lpExtend (𝕜 := 𝕜) (X := X) p sequenceSuccessor).le_of_opNorm_le
        (norm_lpExtend_le (𝕜 := 𝕜) (X := X) (p := p) sequenceSuccessor) x.2
      simpa only [one_mul] using h
    change ‖lp.single (E := fun _ : ℕ => X) p 0 x.1 +
      lpExtend (𝕜 := 𝕜) p sequenceSuccessor x.2‖ ≤ 2 * ‖x‖
    exact (norm_add_le _ _).trans (by nlinarith [norm_fst_le x, norm_snd_le x])

end ThesisCommon
