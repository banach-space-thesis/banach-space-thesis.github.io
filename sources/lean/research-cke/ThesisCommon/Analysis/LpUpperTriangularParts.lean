import ThesisCommon.Analysis.LpSummableEntries
import ThesisCommon.Analysis.SequencePrefixes
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Construct the upper part from an absolutely summable strict-lower
matrix. Every result concerns an actual bounded operator. Uniqueness of
the upper column specification is asserted only for finite p. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def IsLpUpperPart (S U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p) : Prop :=
  ∀ j x, U (lp.single p j x) = lpPrefix j (S (lp.single p j x))

theorem IsLpUpperPart.unique (hp : p ≠ ∞)
    {S U V : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (hU : IsLpUpperPart S U) (hV : IsLpUpperPart S V) : U = V := by
  apply lp.ext_continuousLinearMap hp
  intro j
  ext x k
  exact congrArg (fun y : lp (fun _ : ℕ => X) p => y k) ((hU j x).trans (hV j x).symm)

theorem IsLpUpperPart.entry {S U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p}
    (hU : IsLpUpperPart S U) (i j : ℕ) : lpEntry U i j = if i ≤ j then lpEntry S i j else 0 := by
  ext x
  have h := congrArg (fun y : lp (fun _ : ℕ => X) p => y i) (hU j x)
  by_cases hij : i ≤ j <;> simpa [lpEntry_apply, lpPrefix, hij] using h

variable [CompleteSpace X]

theorem exists_lp_upper_part_of_summable_columns
    (S : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p)
    {δ : ℕ → ℝ} (hδ : Summable δ)
    (hcol : ∀ j, Summable (fun k => ‖lpEntry S (j+1+k) j‖))
    (hbound : ∀ j, (∑' k, ‖lpEntry S (j+1+k) j‖) ≤ δ j) :
    ∃ U : lp (fun _ : ℕ => X) p →L[𝕜] lp (fun _ : ℕ => X) p,
      ‖S-U‖ ≤ ∑' j, δ j ∧ IsLpUpperPart S U := by
  let A : ℕ × ℕ → X →L[𝕜] X := fun a => lpEntry S (a.1+1+a.2) a.1
  have houter : Summable (fun j => ∑' k, ‖lpEntry S (j+1+k) j‖) :=
    hδ.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) hbound
  have hA : Summable (fun a => ‖A a‖) :=
    (summable_prod_of_nonneg (fun a => norm_nonneg (A a))).2 ⟨hcol, houter⟩
  let H := lpSummableEntries p (fun a : ℕ × ℕ => a.1+1+a.2) Prod.fst A
  have hH : ‖H‖ ≤ ∑' j, δ j := by
    apply (norm_lpSummableEntries_le _ _ A hA).trans
    rw [hA.tsum_prod]
    exact houter.tsum_le_tsum hbound hδ
  have happly : ∀ j (x : X) k, H (lp.single p j x) k =
      if k ≤ j then 0 else S (lp.single p j x) k := by
    intro j x k
    rw [lpSummableEntries_apply _ _ _ hA]
    by_cases hkj : k ≤ j
    · rw [if_pos hkj]
      trans ∑' _a : ℕ × ℕ, (0 : X)
      · apply tsum_congr
        intro a
        by_cases haj : a.1 = j
        · have hkr : k ≠ a.1+1+a.2 := by omega
          simp [hkr]
        · simp [haj]
      · simp
    · have hk : j+1+(k-(j+1)) = k := by omega
      rw [if_neg hkj, tsum_eq_single (j, k-(j+1))]
      · simp [A, hk, lpEntry_apply]
      · intro a ha
        by_cases haj : a.1 = j
        · have hkr : k ≠ a.1+1+a.2 := by
            intro h
            apply ha
            apply Prod.ext
            · exact haj
            · dsimp
              omega
          simp [hkr]
        · simp [haj]
  refine ⟨S-H, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using hH
  · intro j x
    apply Subtype.ext
    funext k
    change S (lp.single p j x) k - H (lp.single p j x) k =
      if k ≤ j then S (lp.single p j x) k else 0
    rw [happly]
    split_ifs <;> simp

end ThesisCommon
