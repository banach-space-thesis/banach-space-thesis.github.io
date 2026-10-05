import ThesisCommon.Analysis.IntervalKernelAtoms

/-! A uniform atom dichotomy for T and I-T, with a measurable positive-measure branch. -/
noncomputable section
open MeasureTheory
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem intervalOperatorAtom_complement
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    intervalOperatorAtom (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) t =
      1 - intervalOperatorAtom T t := by
  have heq : T + (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) =
      ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) := by abel
  have h := intervalOperatorAtom_add T (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) t
  rw [heq, intervalOperatorAtom_id] at h
  calc
    _ = (intervalOperatorAtom T t +
        intervalOperatorAtom (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) t) -
          intervalOperatorAtom T t := by abel
    _ = 1 - intervalOperatorAtom T t := by rw [← h]

theorem intervalOperatorAtom_half_dichotomy
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (t : UnitInterval) :
    1 / 2 ≤ ‖intervalOperatorAtom T t‖ ∨
      1 / 2 ≤ ‖intervalOperatorAtom (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) t‖ := by
  rw [intervalOperatorAtom_complement]
  have h : 1 ≤ ‖intervalOperatorAtom T t‖ + ‖1 - intervalOperatorAtom T t‖ := by
    simpa only [add_sub_cancel, norm_one] using
      norm_add_le (intervalOperatorAtom T t) (1 - intervalOperatorAtom T t)
  by_cases ht : 1 / 2 ≤ ‖intervalOperatorAtom T t‖
  · exact Or.inl ht
  · exact Or.inr (by linarith)

theorem intervalOperatorAtom_positive_branch
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (T : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜)
    (ν : Measure UnitInterval) (hν : ν Set.univ ≠ 0) :
    ∃ (Q : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜) (A : Set UnitInterval),
      (Q = T ∨ Q = ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) ∧
      MeasurableSet A ∧ 0 < ν A ∧ ∀ t ∈ A, 1 / 2 ≤ ‖intervalOperatorAtom Q t‖ := by
  let A := {t : UnitInterval | 1 / 2 ≤ ‖intervalOperatorAtom T t‖}
  let B := {t : UnitInterval | 1 / 2 ≤
    ‖intervalOperatorAtom (ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) - T) t‖}
  have hA : MeasurableSet A := measurableSet_le measurable_const (measurable_intervalOperatorAtom T).norm
  have hB : MeasurableSet B := measurableSet_le measurable_const
    (measurable_intervalOperatorAtom _).norm
  have hcover : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    exact intervalOperatorAtom_half_dichotomy T
  have hpos : 0 < ν A ∨ 0 < ν B := by
    by_contra h
    push_neg at h
    have ha : ν A = 0 := le_antisymm h.1 bot_le
    have hb : ν B = 0 := le_antisymm h.2 bot_le
    apply hν
    apply le_antisymm _ bot_le
    rw [← hcover]
    exact (measure_union_le A B).trans_eq (by simp [ha, hb])
  rcases hpos with ha | hb
  · exact ⟨T, A, Or.inl rfl, hA, ha, fun _ ht => ht⟩
  · exact ⟨_, B, Or.inr rfl, hB, hb, fun _ ht => ht⟩

end ThesisCommon
