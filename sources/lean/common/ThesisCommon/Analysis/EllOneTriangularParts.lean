import ThesisCommon.Analysis.EllOneColumnOperators

/-! Actual triangular-part operators on ell1. Their prescribed columns
determine the whole continuous operator because finite supports are dense. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def IsEllOneUpperPart (S U : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) : Prop :=
  ∀ j x, U (lp.single 1 j x) = lpPrefix j (S (lp.single 1 j x))

def IsEllOneLowerPart (S L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) : Prop :=
  ∀ j x, L (lp.single 1 j x) = S (lp.single 1 j x) -
    ∑ i ∈ Finset.range j, lp.single (E := fun _ : ℕ => X) 1 i (lpEntry S i j x)

theorem IsEllOneUpperPart.unique {S U V : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X}
    (hU : IsEllOneUpperPart S U) (hV : IsEllOneUpperPart S V) : U = V := by
  apply lp.ext_continuousLinearMap (by simp : (1 : ℝ≥0∞) ≠ ∞)
  intro j
  ext x k
  exact congrArg (fun y : EllOneSum ℕ X => y k) ((hU j x).trans (hV j x).symm)

theorem IsEllOneLowerPart.unique {S L M : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X}
    (hL : IsEllOneLowerPart S L) (hM : IsEllOneLowerPart S M) : L = M := by
  apply lp.ext_continuousLinearMap (by simp : (1 : ℝ≥0∞) ≠ ∞)
  intro j
  ext x k
  exact congrArg (fun y : EllOneSum ℕ X => y k) ((hL j x).trans (hM j x).symm)

theorem IsEllOneLowerPart.single_apply {S L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X}
    (hL : IsEllOneLowerPart S L) (j : ℕ) (x : X) (k : ℕ) :
    L (lp.single 1 j x) k = if j ≤ k then S (lp.single 1 j x) k else 0 := by
  have h := congrArg (fun y : EllOneSum ℕ X => y k) (hL j x)
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single, Finset.mem_range, lpEntry_apply] at h
  by_cases hjk : j ≤ k
  · simpa [hjk, Nat.not_lt.mpr hjk] using h
  · simpa [hjk, Nat.lt_of_not_ge hjk] using h

/-- The column specification agrees with the whole-operator finite-prefix
definition used elsewhere in the library. -/
theorem IsEllOneLowerPart.isLpLowerPart {S L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X}
    (hL : IsEllOneLowerPart S L) : IsLpLowerPart S L := by
  intro x k
  have hs := (lp.hasSum_single (p := 1) (by simp) x).map
    ((lpCoordinate 1 k).comp L).toAddMonoidHom ((lpCoordinate 1 k).comp L).continuous
  change HasSum (fun j => L (lp.single 1 j (x j)) k) (L x k) at hs
  calc
    L x k = ∑' j, L (lp.single 1 j (x j)) k := hs.tsum_eq.symm
    _ = ∑ j ∈ Finset.range (k+1), L (lp.single 1 j (x j)) k := tsum_eq_sum (fun j hj => by
      rw [hL.single_apply]
      have hgt : k < j := by simpa only [Finset.mem_range, Nat.lt_succ_iff, not_le] using hj
      simp [Nat.not_le.mpr hgt])
    _ = ∑ j ∈ Finset.range (k+1), S (lp.single 1 j (x j)) k := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hL.single_apply, if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    _ = S (lpPrefix k x) k := by
      rw [lpPrefix_eq_sum_single, map_sum]
      change _ = (lpCoordinate (𝕜 := 𝕜) 1 k) (∑ j ∈ Finset.range (k+1), S (lp.single 1 j (x j)))
      rw [map_sum]
      rfl

def ellOneEarlierColumn (S : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) (j : ℕ) :
    X →L[𝕜] EllOneSum ℕ X :=
  ∑ i ∈ Finset.range j,
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 i).comp (lpEntry S i j)

theorem ellOneEarlierColumn_apply (S : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) (j : ℕ) (x : X) :
    ellOneEarlierColumn S j x =
      ∑ i ∈ Finset.range j, lp.single (E := fun _ : ℕ => X) 1 i (lpEntry S i j x) := by
  simp only [ellOneEarlierColumn, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]

theorem norm_ellOneEarlierColumn_le (S : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) (j : ℕ) :
    ‖ellOneEarlierColumn S j‖ ≤ ∑ i ∈ Finset.range j, ‖lpEntry S i j‖ := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun i _ => norm_comp_left_contraction _ (norm_lpSingleCLM_le i) _)

variable [CompleteSpace X]

/-- A uniform output-tail column bound yields a close actual upper part. -/
theorem exists_ellOne_upper_part
    (S : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) {b : ℝ} (hb : 0 ≤ b)
    (htail : ∀ j, ‖((lpRestrict 1 (coordinateTail (Function.Embedding.refl ℕ) j)).comp S).comp
      (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j)‖ ≤ b) :
    ∃ U : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X, ‖S-U‖ ≤ b ∧ IsEllOneUpperPart S U := by
  let s := fun j => coordinateTail (Function.Embedding.refl ℕ) j
  let F : ℕ → X →L[𝕜] EllOneSum ℕ X := fun j => (lpExtend 1 (s j)).comp
    (((lpRestrict 1 (s j)).comp S).comp (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => X) 1 j))
  have hF : ∀ j, ‖F j‖ ≤ b := fun j =>
    (norm_comp_left_contraction _ (norm_lpExtend_le (s j)) _).trans (htail j)
  let H := ellOneColumns F b hb hF
  refine ⟨S-H, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using norm_ellOneColumns_le F b hb hF
  · intro j x
    change S (lp.single 1 j x) - H (lp.single 1 j x) = _
    rw [ellOneColumns_single]
    have h := lpPrefix_add_tail (𝕜 := 𝕜) j (S (lp.single 1 j x))
    exact (eq_sub_of_add_eq h).symm

/-- Summable earlier entries give a close actual lower part. -/
theorem exists_ellOne_lower_part
    (S : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X) {b : ℝ} (hb : 0 ≤ b)
    (hearlier : ∀ j, (∑ i ∈ Finset.range j, ‖lpEntry S i j‖) ≤ b) :
    ∃ L : EllOneSum ℕ X →L[𝕜] EllOneSum ℕ X, ‖S-L‖ ≤ b ∧ IsEllOneLowerPart S L := by
  have hF : ∀ j, ‖ellOneEarlierColumn S j‖ ≤ b := fun j =>
    (norm_ellOneEarlierColumn_le S j).trans (hearlier j)
  let H := ellOneColumns (ellOneEarlierColumn S) b hb hF
  refine ⟨S-H, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using norm_ellOneColumns_le (ellOneEarlierColumn S) b hb hF
  · intro j x
    change S (lp.single 1 j x) - H (lp.single 1 j x) = _
    rw [ellOneColumns_single, ellOneEarlierColumn_apply]

end ThesisCommon
