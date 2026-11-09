import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! # The Daugavet slice criterion over the real and complex scalar fields

The geometric slice condition implies the norm identity for every bounded
rank-one operator. Rank-one maps are written as `φ.smulRight y`.
-/

noncomputable section
namespace PL1.Daugavet

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The usual geometric criterion, phrased with real parts for either scalar field. -/
def SliceCriterion (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∀ h : E, ‖h‖ = 1 → ∀ φ : E →L[𝕜] 𝕜, ‖φ‖ = 1 → ∀ ε : ℝ, 0 < ε →
    ∃ x : E, ‖x‖ ≤ 1 ∧ 1 - ε < RCLike.re (φ x) ∧ 2 - ε < ‖h + x‖

/-- The Daugavet norm identity for the actual bounded rank-one maps. -/
def HasDaugavetProperty (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] : Prop :=
  ∀ (φ : E →L[𝕜] 𝕜) (y : E),
    ‖ContinuousLinearMap.id 𝕜 E + φ.smulRight y‖ = 1 + ‖φ.smulRight y‖

private theorem norm_sub_one_lt (z : 𝕜) (hz : ‖z‖ ≤ 1) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : δ ≤ ε ^ 2 / 2) (hre : 1 - δ < RCLike.re z) : ‖z - 1‖ < ε := by
  have hs : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 + 1 - 2 * RCLike.re z := by
    simpa only [RCLike.normSq_eq_def', norm_one, one_pow, map_one, mul_one] using
      RCLike.normSq_sub z 1
  have hzn := norm_nonneg z
  have hdn := norm_nonneg (z - 1)
  nlinarith

/-- A sufficiently thin real-part slice also controls the complex phase. -/
theorem SliceCriterion.exists_near_one (hs : SliceCriterion 𝕜 E)
    (h : E) (hh : ‖h‖ = 1) (φ : E →L[𝕜] 𝕜) (hφ : ‖φ‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖φ x - 1‖ < ε ∧ 2 - ε < ‖h + x‖ := by
  let δ := min ε (ε ^ 2 / 2)
  have hδ : 0 < δ := lt_min hε (by positivity)
  obtain ⟨x, hx, hφx, hsum⟩ := hs h hh φ hφ δ hδ
  refine ⟨x, hx, norm_sub_one_lt (φ x) ?_ ε δ hε (min_le_right _ _) hφx, ?_⟩
  · exact (φ.le_opNorm x).trans (by simpa only [hφ, one_mul] using hx)
  · exact lt_of_le_of_lt (by dsimp [δ]; linarith [min_le_left ε (ε ^ 2 / 2)]) hsum

private theorem weighted_separation (h x : E) (hh : ‖h‖ = 1) (hx : ‖x‖ ≤ 1)
    (ε t : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) (hs : 2 - ε < ‖h + x‖) :
    1 + t - (1 + t) * ε < ‖x + (t : 𝕜) • h‖ := by
  by_cases ht1 : t ≤ 1
  · have he : x + h = (x + (t : 𝕜) • h) + ((1 - t : ℝ) : 𝕜) • h := by
      simp only [RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
      abel
    have hn := norm_add_le (x + (t : 𝕜) • h) (((1 - t : ℝ) : 𝕜) • h)
    rw [← he, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (sub_nonneg.mpr ht1), hh, mul_one] at hn
    rw [add_comm h x] at hs
    nlinarith [mul_nonneg ht hε.le]
  · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have he : (t : 𝕜) • (x + h) =
        (x + (t : 𝕜) • h) + ((t - 1 : ℝ) : 𝕜) • x := by
      simp only [smul_add, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
      abel
    have hn := norm_add_le (x + (t : 𝕜) • h) (((t - 1 : ℝ) : 𝕜) • x)
    rw [← he, norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal,
      abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht1')] at hn
    rw [add_comm h x] at hs
    have hm := mul_lt_mul_of_pos_left hs (show 0 < t by linarith)
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht1')
    nlinarith

private theorem norm_id_add_scaled_rankOne [Nontrivial E]
    (hs : SliceCriterion 𝕜 E) (h : E) (hh : ‖h‖ = 1)
    (φ : E →L[𝕜] 𝕜) (hφ : ‖φ‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    ‖ContinuousLinearMap.id 𝕜 E + (t : 𝕜) • φ.smulRight h‖ = 1 + t := by
  let T : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E + (t : 𝕜) • φ.smulRight h
  have hupper : ‖T‖ ≤ 1 + t := by
    calc
      _ ≤ ‖ContinuousLinearMap.id 𝕜 E‖ + ‖(t : 𝕜) • φ.smulRight h‖ := norm_add_le _ _
      _ = _ := by simp [norm_smul, abs_of_nonneg ht,
        ContinuousLinearMap.norm_smulRight_apply, hφ, hh]
  have hlower (ε : ℝ) (hε : 0 < ε) : 1 + t - ε < ‖T‖ := by
    let δ := ε / (1 + 2 * t)
    have hd : 0 < δ := div_pos hε (by linarith)
    obtain ⟨x, hx, hφx, hsum⟩ := hs.exists_near_one h hh φ hφ δ hd
    have hw := weighted_separation (𝕜 := 𝕜) h x hh hx δ t hd ht hsum
    have he : (x + (t : 𝕜) • h) - T x = -((t : 𝕜) • ((φ x - 1) • h)) := by
      simp only [T, add_apply, ContinuousLinearMap.id_apply,
        smul_apply, ContinuousLinearMap.smulRight_apply,
        sub_smul, smul_sub, one_smul]
      abel
    have hn := norm_sub_norm_le (x + (t : 𝕜) • h) (T x)
    rw [he, norm_neg, norm_smul, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg ht, hh, mul_one] at hn
    have hm := mul_le_mul_of_nonneg_left hφx.le ht
    have hTx : ‖T x‖ ≤ ‖T‖ :=
      (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg T) hx)
    have hδeq : (1 + 2 * t) * δ = ε := by
      dsimp [δ]
      field_simp
    nlinarith
  apply le_antisymm hupper
  by_contra hn
  have he : 0 < (1 + t - ‖T‖) / 2 := by linarith
  have h := hlower ((1 + t - ‖T‖) / 2) he
  linarith

/-- The geometric slice criterion implies the Daugavet norm equation for every rank-one map. -/
theorem SliceCriterion.hasDaugavetProperty [Nontrivial E] (hs : SliceCriterion 𝕜 E) :
    HasDaugavetProperty 𝕜 E := by
  intro φ y
  by_cases hφ : φ = 0
  · simp [hφ]
  by_cases hy : y = 0
  · simp [hy]
  have hφn : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  let ψ : E →L[𝕜] 𝕜 := ((‖φ‖⁻¹ : ℝ) : 𝕜) • φ
  let h : E := ((‖y‖⁻¹ : ℝ) : 𝕜) • y
  have hψ : ‖ψ‖ = 1 := by
    simp [ψ, norm_smul,
      inv_mul_cancel₀ hφn]
  have hh : ‖h‖ = 1 := by
    simp [h, norm_smul,
      inv_mul_cancel₀ hyn]
  have hφK : (‖φ‖ : 𝕜) ≠ 0 := by exact_mod_cast hφn
  have hyK : (‖y‖ : 𝕜) ≠ 0 := by exact_mod_cast hyn
  have he : (((‖φ‖ * ‖y‖ : ℝ) : 𝕜) • ψ.smulRight h) = φ.smulRight y := by
    ext x
    simp only [ψ, h, smul_apply, ContinuousLinearMap.smulRight_apply,
      smul_smul, smul_eq_mul, RCLike.ofReal_mul, RCLike.ofReal_inv]
    congr 1
    field_simp
  have hn := norm_id_add_scaled_rankOne hs h hh ψ hψ (‖φ‖ * ‖y‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [he] at hn
  simpa only [ContinuousLinearMap.norm_smulRight_apply] using hn

#print axioms SliceCriterion.hasDaugavetProperty

end PL1.Daugavet
