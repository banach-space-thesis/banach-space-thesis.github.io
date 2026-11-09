import ThesisCommon.Analysis.CotypeBackwardSelection
import ThesisCommon.Analysis.SequencePrefixes
import ThesisCommon.Analysis.CZeroSingles
import ThesisCommon.Analysis.SupRowOperators
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual lower-triangular approximation, UPFP Proposition 4.7.
Subtract the operator formed by each row's infinite-tail action. Thus the
argument works on all bounded sequences without assuming matrix determination.
-/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Actual lower-triangular action: row k applies S to the finite prefix
0,...,k of its input. This specifies the whole operator, including on ℓ∞. -/
def IsLpLowerPart {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) : Prop :=
  ∀ x k, L x k = S (lpPrefix k x) k

/-- The corresponding whole-operator definition on null sequences. -/
def IsCZeroLowerPart (S L : CZeroSum X →L[𝕜] CZeroSum X) : Prop :=
  ∀ x k, L x k = S (cZeroPrefix k x) k

/-- The prefix definition is exactly the finite lower-triangular matrix sum. -/
theorem IsLpLowerPart.matrix_formula {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {S L : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (h : IsLpLowerPart S L) (x : lp (fun _ : ℕ => X) p) (k : ℕ) :
    L x k = ∑ j ∈ Finset.range (k + 1), S (lp.single p j (x j)) k := by
  rw [h x k, lpPrefix_eq_sum_single, map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply]

/-- On c₀ too, finite-prefix action is the finite lower matrix sum. -/
theorem IsCZeroLowerPart.matrix_formula
    {S L : CZeroSum X →L[𝕜] CZeroSum X}
    (h : IsCZeroLowerPart S L) (x : CZeroSum X) (k : ℕ) :
    L x k = ∑ j ∈ Finset.range (k + 1), S (cZeroSingle j (x j)) k := by
  rw [h x k, cZeroPrefix_eq_sum_single, map_sum]
  change (cZeroCoordinate (𝕜 := 𝕜) k) (∑ j ∈ Finset.range (k + 1), S (cZeroSingle j (x j))) = _
  rw [map_sum]
  rfl

/-- Finite cotype supplies an arbitrarily close lower-triangular approximation
after an increasing coordinate compression of an arbitrary ℓ∞ operator. -/
theorem HasFiniteCotype.infinity_lower_triangular (h : HasFiniteCotype X)
    (T : EllInfinitySum X →L[𝕜] EllInfinitySum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (L : EllInfinitySum X →L[𝕜] EllInfinitySum X),
      StrictMono e ∧
      ‖((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e) - L‖ < ε ∧
      IsLpLowerPart (((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e)) L := by
  let δ : ℕ → ℝ := fun k => (ε / 2) * (1 / 2 : ℝ) ^ k
  have hδ : ∀ k, 0 < δ k := fun k => by dsimp [δ]; positivity
  have hδbound : ∀ k, δ k ≤ ε / 2 := by
    intro k
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)) (by positivity)).trans_eq (mul_one _)
  obtain ⟨e, hmono, he⟩ := h.infinity_backward_selection T δ hδ
  let shift := fun k => coordinateTail (Function.Embedding.refl ℕ) k
  let R : ℕ → EllInfinitySum X →L[𝕜] X := fun k =>
    (((lpCoordinate ∞ (e k)).comp T).comp (lpExtend ∞ (coordinateTail e k))).comp
      (lpRestrict (𝕜 := 𝕜) ∞ (shift k))
  have hR : ∀ k, ‖R k‖ ≤ δ k := by
    intro k
    calc
      _ ≤ ‖((lpCoordinate ∞ (e k)).comp T).comp (lpExtend ∞ (coordinateTail e k))‖ *
          ‖lpRestrict (𝕜 := 𝕜) (X := X) ∞ (shift k)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ δ k * 1 := mul_le_mul (he k).le (norm_lpRestrict_le (shift k)) (norm_nonneg _) (hδ k).le
      _ = δ k := mul_one _
  let H := infinityRows R (ε / 2) (by positivity) (fun k => (hR k).trans (hδbound k))
  let S := ((lpRestrict ∞ e).comp T).comp (lpExtend ∞ e)
  refine ⟨e, S - H, hmono, ?_, ?_⟩
  · change ‖S - (S - H)‖ < ε
    rw [sub_sub_cancel]
    exact (norm_infinityRows_le _ _ _ _).trans_lt (by linarith)
  · intro x k
    change T (lpExtend ∞ e x) (e k) - R k x = T (lpExtend ∞ e (lpPrefix k x)) (e k)
    have hs := congrArg (fun y : EllInfinitySum X => T (lpExtend (𝕜 := 𝕜) ∞ e y) (e k))
      (lpPrefix_add_tail (𝕜 := 𝕜) k x)
    simp only [map_add, lp.coeFn_add, Pi.add_apply] at hs
    have hj : lpExtend (𝕜 := 𝕜) ∞ e (lpExtend (𝕜 := 𝕜) ∞ (shift k) (lpRestrict (𝕜 := 𝕜) ∞ (shift k) x)) =
        lpExtend ∞ (coordinateTail e k) (lpRestrict (𝕜 := 𝕜) ∞ (shift k) x) :=
      congrArg (fun A : EllInfinitySum X →L[𝕜] EllInfinitySum X => A (lpRestrict (𝕜 := 𝕜) ∞ (shift k) x))
        (lpExtend_comp (shift k) e)
    rw [hj] at hs
    exact sub_eq_iff_eq_add.mpr hs.symm

/-- The same construction lands in c₀ because its row norms tend to zero. -/
theorem HasFiniteCotype.cZero_lower_triangular (h : HasFiniteCotype X)
    (T : CZeroSum X →L[𝕜] CZeroSum X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (L : CZeroSum X →L[𝕜] CZeroSum X), StrictMono e ∧
      ‖((cZeroRestrict e).comp T).comp (cZeroExtend e) - L‖ < ε ∧
      IsCZeroLowerPart (((cZeroRestrict e).comp T).comp (cZeroExtend e)) L := by
  let δ : ℕ → ℝ := fun k => (ε / 2) * (1 / 2 : ℝ) ^ k
  have hδ : ∀ k, 0 < δ k := fun k => by dsimp [δ]; positivity
  have hδbound : ∀ k, δ k ≤ ε / 2 := by
    intro k
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)) (by positivity)).trans_eq (mul_one _)
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (ε / 2)
  obtain ⟨e, hmono, he⟩ := h.cZero_backward_selection T δ hδ
  let shift := fun k => coordinateTail (Function.Embedding.refl ℕ) k
  let R : ℕ → CZeroSum X →L[𝕜] X := fun k =>
    (((cZeroCoordinate (e k)).comp T).comp (cZeroExtend (coordinateTail e k))).comp
      (cZeroRestrict (𝕜 := 𝕜) (shift k))
  have hR : ∀ k, ‖R k‖ ≤ δ k := by
    intro k
    calc
      _ ≤ ‖((cZeroCoordinate (e k)).comp T).comp (cZeroExtend (coordinateTail e k))‖ *
          ‖cZeroRestrict (𝕜 := 𝕜) (X := X) (shift k)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ δ k * 1 := mul_le_mul (he k).le (norm_cZeroRestrict_le (shift k))
        (norm_nonneg (cZeroRestrict (𝕜 := 𝕜) (X := X) (shift k))) (hδ k).le
      _ = δ k := mul_one _
  have hRzero : Tendsto (fun k => ‖R k‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg (R k)) hR hδzero
  let H := cZeroRows R (ε / 2) (by positivity) (fun k => (hR k).trans (hδbound k)) hRzero
  let S := ((cZeroRestrict e).comp T).comp (cZeroExtend e)
  refine ⟨e, S - H, hmono, ?_, ?_⟩
  · change ‖S - (S - H)‖ < ε
    rw [sub_sub_cancel]
    exact (norm_cZeroRows_le _ _ _ _ _).trans_lt (by linarith)
  · intro x k
    change T (cZeroExtend e x) (e k) - R k x = T (cZeroExtend e (cZeroPrefix k x)) (e k)
    have hs := congrArg (fun y : CZeroSum X => T (cZeroExtend (𝕜 := 𝕜) e y) (e k))
      (cZeroPrefix_add_tail (𝕜 := 𝕜) k x)
    simp only [map_add, ZeroAtInftyContinuousMap.add_apply] at hs
    have hj : cZeroExtend (𝕜 := 𝕜) e (cZeroExtend (𝕜 := 𝕜) (shift k) (cZeroRestrict (𝕜 := 𝕜) (shift k) x)) =
        cZeroExtend (coordinateTail e k) (cZeroRestrict (𝕜 := 𝕜) (shift k) x) :=
      congrArg (fun A : CZeroSum X →L[𝕜] CZeroSum X => A (cZeroRestrict (𝕜 := 𝕜) (shift k) x))
        (cZeroExtend_comp (shift k) e)
    rw [hj] at hs
    exact sub_eq_iff_eq_add.mpr hs.symm

end ThesisCommon
