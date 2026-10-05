import ThesisCommon.Analysis.SchauderSumOperators

/-! Genuine restriction and zero extension of vector-valued sequences along
an injection. Symmetry of the outer norm makes extension isometric and
restriction contractive, with no assumption on the inner basis.
-/
noncomputable section
open scoped Classical
namespace ThesisCommon
namespace NormalizedSchauderBasis
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (b : NormalizedSchauderBasis 𝕜 X)

theorem coord_subsequence_insertion (f : ℕ ↪ ℕ) (B : X →L[𝕜] X)
    (hB : ∀ n, B (b.vector n) = b.vector (f n)) (i : ℕ) (x : X) :
    b.coord i (B x) = if i ∈ Set.range f then b.coord (Function.invFun f i) x else 0 := by
  classical
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hi
    have heq : (b.coord (f j)).comp B = b.coord j := by
      apply b.operator_ext
      intro n
      simp only [ContinuousLinearMap.comp_apply, hB, b.biorthogonal, f.injective.eq_iff]
    rw [if_pos (Set.mem_range_self j), Function.leftInverse_invFun f.injective j]
    exact DFunLike.congr_fun heq x
  · have heq : (b.coord i).comp B = 0 := by
      apply b.operator_ext
      intro n
      have hne : i ≠ f n := fun h => hi ⟨n, h.symm⟩
      simp only [ContinuousLinearMap.comp_apply, hB, b.biorthogonal, if_neg hne,
        ContinuousLinearMap.zero_apply]
    rw [if_neg hi]
    exact DFunLike.congr_fun heq x
end NormalizedSchauderBasis

namespace SchauderSum
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable {b : NormalizedSchauderBasis 𝕜 X} {hb : b.IsOneUnconditional}

/-- Actual zero extension along an injection of outer coordinates. -/
def extend (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) (y : SchauderSum b hb Y) :
    SchauderSum b hb Y := ⟨fun i => if i ∈ Set.range f then y (Function.invFun f i) else 0, by
  obtain ⟨B, _, _, hB⟩ := b.exists_subsequence_insertion hs f
  refine ⟨B (normVector y), ?_⟩
  intro i
  dsimp only
  rw [b.coord_subsequence_insertion f B hB]
  split_ifs with hi
  · exact coord_normVector y _
  · simp⟩

theorem extend_apply (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ)
    (y : SchauderSum b hb Y) (i : ℕ) :
    extend hs f y i = if i ∈ Set.range f then y (Function.invFun f i) else 0 := rfl

theorem norm_extend (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) (y : SchauderSum b hb Y) :
    ‖extend hs f y‖ = ‖y‖ := by
  obtain ⟨B, _, hn, hB⟩ := b.exists_subsequence_insertion hs f
  have heq : normVector (extend hs f y) = B (normVector y) := by
    apply normVector_eq
    intro i
    rw [b.coord_subsequence_insertion f B hB, extend_apply]
    split_ifs with hi
    · exact coord_normVector y _
    · simp
  rw [norm_def, heq, hn, norm_def]

/-- The actual zero-extension operator, with norm-preserving action. -/
def extendL (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) :
    SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y :=
  LinearMap.mkContinuous
    { toFun := extend hs f
      map_add' := by
        intro y z; ext i
        by_cases hi : i ∈ Set.range f <;> simp [extend_apply, hi]
      map_smul' := by
        intro a y; ext i
        by_cases hi : i ∈ Set.range f <;> simp [extend_apply, hi] }
    1 (fun y => by change ‖extend hs f y‖ ≤ 1 * ‖y‖; rw [norm_extend, one_mul])

theorem extendL_apply (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) (y : SchauderSum b hb Y) :
    extendL (hb := hb) (Y := Y) hs f y = extend hs f y := rfl

theorem extendL_single (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) (n : ℕ) (y : Y) :
    extendL (hb := hb) (Y := Y) hs f (single n y) = single (f n) y := by
  classical
  ext i
  rw [extendL_apply, extend_apply, single_apply]
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hi
    rw [if_pos (Set.mem_range_self j), Function.leftInverse_invFun f.injective j, single_apply]
    simp only [f.injective.eq_iff]
  · have hne : i ≠ f n := fun h => hi ⟨n, h.symm⟩
    simp only [if_neg hi, single_apply, if_neg hne]

/-- Actual restriction of a vector-valued sequence to selected coordinates. -/
def restrict (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) (y : SchauderSum b hb Y) :
    SchauderSum b hb Y := ⟨fun i => y (f i), by
  obtain ⟨A, _, _, _, _, _, hA⟩ := b.exists_subsequence_compression hs f
  exact ⟨A (normVector y), fun i => (hA i _).trans (coord_normVector y (f i))⟩⟩

theorem restrict_apply (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ)
    (y : SchauderSum b hb Y) (i : ℕ) : restrict hs f y i = y (f i) := rfl

theorem norm_restrict_le (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) (y : SchauderSum b hb Y) :
    ‖restrict hs f y‖ ≤ ‖y‖ := by
  obtain ⟨A, _, _, hn, _, _, hA⟩ := b.exists_subsequence_compression hs f
  have heq : normVector (restrict hs f y) = A (normVector y) :=
    normVector_eq _ _ (fun i => (hA i _).trans (coord_normVector y (f i)))
  rw [norm_def, heq]
  exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))

def restrictL (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) :
    SchauderSum b hb Y →L[𝕜] SchauderSum b hb Y :=
  LinearMap.mkContinuous
    { toFun := restrict hs f
      map_add' := by intro y z; ext i; rfl
      map_smul' := by intro a y; ext i; rfl }
    1 (fun y => by simpa only [one_mul] using norm_restrict_le hs f y)

theorem restrictL_apply (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ)
    (y : SchauderSum b hb Y) (i : ℕ) : restrictL (hb := hb) (Y := Y) hs f y i = y (f i) := rfl

theorem norm_restrictL_le (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) :
    ‖restrictL (hb := hb) (Y := Y) hs f‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_extendL_le (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ) :
    ‖extendL (hb := hb) (Y := Y) hs f‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem restrictL_extendL (hs : b.HasSymmetricNorm) (f : ℕ ↪ ℕ)
    (y : SchauderSum b hb Y) : restrictL (hb := hb) (Y := Y) hs f
      (extendL (hb := hb) (Y := Y) hs f y) = y := by
  ext i
  rw [restrictL_apply, extendL_apply, extend_apply, if_pos (Set.mem_range_self i),
    Function.leftInverse_invFun f.injective i]

end SchauderSum
end ThesisCommon
