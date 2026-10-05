import ThesisCommon.Analysis.UncountableSchauderReindexing
import ThesisCommon.Analysis.UncountableSchauderDiagonalSelection

/-! Exact matrix compression on the actual arbitrary-index norm-series sum.
Operator identities are proved on single-coordinate vectors and then passed
to the whole space through the convergent net of finite truncations. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon.UncountableSchauderSum
attribute [local instance] Classical.propDecidable
variable {𝕜 Γ E X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderFamily 𝕜 Γ E} {hb : b.IsOneUnconditional}

theorem operator_ext_single {S T : UncountableSchauderSum b hb X →L[𝕜] Y}
    (h : ∀ i x, S (single i x) = T (single i x)) : S = T := by
  apply ContinuousLinearMap.ext
  intro x
  have hs := (S.continuous.tendsto x).comp (expansion x)
  have ht := (T.continuous.tendsto x).comp (expansion x)
  apply tendsto_nhds_unique hs
  convert ht using 1
  funext F
  simp only [Function.comp_apply, map_sum, h]

/-- A matrix entry acting on the actual coefficient space. -/
def fibreEntry
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) : X →L[𝕜] X := ((coordinate β).comp T).comp (singleL α)

@[simp] theorem fibreEntry_apply
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) (x : X) : fibreEntry T β α x = T (single α x) β := rfl

theorem norm_fibreEntry_le
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) : ‖fibreEntry T β α‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  exact (norm_apply_le (T (single α x)) β).trans
    (by simpa only [norm_single] using T.le_opNorm (single α x))

theorem fibreEntry_eq_zero_of_coordinateEntry_eq_zero
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (β α : Γ) (h : coordinateEntry T β α = 0) : fibreEntry T β α = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun S : UncountableSchauderSum b hb X →L[𝕜]
      UncountableSchauderSum b hb X => S (single α x) β) h
  simpa only [coordinateEntry_apply, single_apply, if_pos rfl,
    ContinuousLinearMap.zero_apply, zero_apply] using hx

@[simp] theorem fibreEntry_complement_diagonal
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X) (α : Γ) :
    fibreEntry (ContinuousLinearMap.id 𝕜 _ - T) α α =
      ContinuousLinearMap.id 𝕜 X - fibreEntry T α α := by
  ext x
  simp only [fibreEntry_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, sub_apply, single_apply, ite_true]

theorem fibreEntry_complement_offDiagonal
    (T : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    {β α : Γ} (h : β ≠ α) :
    fibreEntry (ContinuousLinearMap.id 𝕜 _ - T) β α = -fibreEntry T β α := by
  ext x
  simp only [fibreEntry_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, sub_apply, single_apply, if_neg h,
    zero_sub, ContinuousLinearMap.neg_apply]

theorem reindexed_insertion_single (f : Γ ↪ Γ)
    (B : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (hB : ∀ x j, B x j = if h : j ∈ Set.range f then x h.choose else 0)
    (i : Γ) (x : X) : B (single i x) = single (f i) x := by
  classical
  ext j
  rw [hB, single_apply]
  by_cases hj : j ∈ Set.range f
  · rw [dif_pos hj, single_apply]
    have he : hj.choose = i ↔ j = f i := by
      constructor
      · intro h; exact hj.choose_spec.symm.trans (congrArg f h)
      · intro h; exact f.injective (hj.choose_spec.trans h)
    simp only [he]
  · have hi : j ≠ f i := fun h => hj ⟨i, h.symm⟩
    simp only [dif_neg hj, if_neg hi]

/-- Off-diagonal vanishing on the selected coordinates gives an exact
diagonal compression, with no approximation error or abstract map axiom. -/
theorem compression_eq_diagonal (f : Γ ↪ Γ)
    (T A B : UncountableSchauderSum b hb X →L[𝕜] UncountableSchauderSum b hb X)
    (hA : ∀ x i, A x i = x (f i))
    (hB : ∀ x j, B x j = if h : j ∈ Set.range f then x h.choose else 0)
    (hoff : ∀ i j, i ≠ j → fibreEntry T (f j) (f i) = 0) :
    (A.comp T).comp B = diagonal (fun i => fibreEntry T (f i) (f i))
      ‖T‖ (norm_nonneg T) (fun i => norm_fibreEntry_le T (f i) (f i)) := by
  apply operator_ext_single
  intro i x
  ext j
  simp only [ContinuousLinearMap.comp_apply, hA, reindexed_insertion_single f B hB,
    diagonal_apply, single_apply]
  by_cases h : j = i
  · subst j
    simp only [ite_true, fibreEntry_apply]
  · rw [if_neg h, map_zero]
    have hz := DFunLike.congr_fun (hoff i j (Ne.symm h)) x
    exact hz

end ThesisCommon.UncountableSchauderSum
