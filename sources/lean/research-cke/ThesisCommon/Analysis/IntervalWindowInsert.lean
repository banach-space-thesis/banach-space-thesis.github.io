import ThesisCommon.Analysis.IntervalWindows
import ThesisCommon.Analysis.ContinuousMapCutoff
import ThesisCommon.Analysis.ContinuousMapCZeroBlocks

/-! Place one C[0,1] function in each disjoint window, retaining it on the
inner interval and tapering it continuously to zero outside the window. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def intervalWindowInsert (n : ℕ) : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
  (continuousMapCutoff (intervalWindowCutoff n) (intervalWindowCutoff_bounds n)).comp
    (intervalInsert (intervalWindow n))

theorem norm_intervalWindowInsert_le (n : ℕ) : ‖intervalWindowInsert (𝕜 := 𝕜) n‖ ≤ 1 := by
  exact (norm_comp_left_contraction (𝕜 := 𝕜)
    (X := IntervalContinuous 𝕜) (Y := IntervalContinuous 𝕜) (Z := IntervalContinuous 𝕜)
    (continuousMapCutoff (intervalWindowCutoff n) (intervalWindowCutoff_bounds n))
    (norm_continuousMapCutoff_le (𝕜 := 𝕜) (intervalWindowCutoff n) (intervalWindowCutoff_bounds n))
    (intervalInsert (𝕜 := 𝕜) (intervalWindow n))).trans (norm_intervalInsert_le (intervalWindow n))

theorem intervalWindowInsert_zero (n : ℕ) (f : IntervalContinuous 𝕜) {t : UnitInterval}
    (ht : t ∉ intervalWindowOpen n) : intervalWindowInsert n f t = 0 := by
  simp only [intervalWindowInsert, ContinuousLinearMap.comp_apply, continuousMapCutoff_apply,
    intervalWindowCutoff_zero n ht, RCLike.ofReal_zero, zero_mul]

theorem intervalRead_windowInsert (n : ℕ) :
    (intervalRead (𝕜 := 𝕜) (intervalWindow n)).comp (intervalWindowInsert n) =
      ContinuousLinearMap.id 𝕜 _ := by
  ext f t
  let e := unitSubintervalHomeomorph (intervalWindowLeft n) (intervalWindowRight n) (intervalWindow n).property
  change (intervalWindowCutoff n (e t).val : 𝕜) * intervalInsert (intervalWindow n) f (e t).val = f t
  rw [intervalWindowCutoff_one n (e t).property, RCLike.ofReal_one, one_mul]
  exact congrArg (fun A : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 => A f t)
    (intervalRead_comp_insert (intervalWindow n))

theorem intervalWindowInsert_disjoint (i j : ℕ) (hij : i ≠ j)
    (f g : IntervalContinuous 𝕜) (t : UnitInterval) :
    intervalWindowInsert i f t = 0 ∨ intervalWindowInsert j g t = 0 := by
  by_cases ht : t ∈ intervalWindowOpen i
  · right
    apply intervalWindowInsert_zero
    exact fun hj => Set.disjoint_left.1 (intervalWindowOpen_disjoint hij) ht hj
  · exact Or.inl (intervalWindowInsert_zero i f ht)

def intervalCZeroInsert : CZeroSum (IntervalContinuous 𝕜) →L[𝕜] IntervalContinuous 𝕜 :=
  continuousMapCZeroInsert intervalWindowInsert norm_intervalWindowInsert_le intervalWindowInsert_disjoint

theorem norm_intervalCZeroInsert_le : ‖intervalCZeroInsert (𝕜 := 𝕜)‖ ≤ 1 :=
  norm_continuousMapCZeroInsert_le ..

theorem intervalCZeroInsert_single (n : ℕ) (f : IntervalContinuous 𝕜) :
    intervalCZeroInsert (cZeroSingle n f) = intervalWindowInsert n f := continuousMapCZeroInsert_single ..

end ThesisCommon
