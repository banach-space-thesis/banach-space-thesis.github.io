import ThesisCommon.Analysis.IntervalBackwardReduction
import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Identify every chosen nondegenerate interval copy with [0,1]. The
resulting read and extension maps are contractions with exact retraction. -/
noncomputable section
open scoped ENNReal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev NondegenerateUnitSubinterval :=
  {ab : UnitInterval × UnitInterval // ab.1 < ab.2}

def intervalRead (c : NondegenerateUnitSubinterval) : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
  let e := unitSubintervalHomeomorph c.val.1 c.val.2 c.property
  continuousMapPullback ⟨fun t => (e t).val, continuous_subtype_val.comp e.continuous⟩

def intervalInsert (c : NondegenerateUnitSubinterval) : IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜 :=
  let e := unitSubintervalHomeomorph c.val.1 c.val.2 c.property
  continuousMapPullback ⟨fun t => e.symm (Set.projIcc c.val.1 c.val.2 c.property.le t),
    e.symm.continuous.comp continuous_projIcc⟩

theorem norm_intervalRead_le (c : NondegenerateUnitSubinterval) :
    ‖intervalRead (𝕜 := 𝕜) c‖ ≤ 1 := norm_continuousMapPullback_le _

theorem norm_intervalInsert_le (c : NondegenerateUnitSubinterval) :
    ‖intervalInsert (𝕜 := 𝕜) c‖ ≤ 1 := norm_continuousMapPullback_le _

theorem intervalRead_comp_insert (c : NondegenerateUnitSubinterval) :
    (intervalRead (𝕜 := 𝕜) c).comp (intervalInsert c) =
      ContinuousLinearMap.id 𝕜 (IntervalContinuous 𝕜) := by
  ext f t
  let e := unitSubintervalHomeomorph c.val.1 c.val.2 c.property
  change f (e.symm (Set.projIcc c.val.1 c.val.2 c.property.le (e t).val)) = f t
  rw [Set.projIcc_of_mem c.property.le (e t).property, e.symm_apply_apply]

theorem norm_intervalRead_comp_le {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (c : NondegenerateUnitSubinterval) (T : X →L[𝕜] IntervalContinuous 𝕜) :
    ‖(intervalRead c).comp T‖ ≤
      ‖(continuousMapRestrict (Set.Icc c.val.1 c.val.2)).comp T‖ := by
  let e := unitSubintervalHomeomorph c.val.1 c.val.2 c.property
  have heq : intervalRead (𝕜 := 𝕜) c =
      (continuousMapPullback ⟨e, e.continuous⟩).comp
        (continuousMapRestrict (Set.Icc c.val.1 c.val.2)) := by
    ext f t
    rfl
  rw [heq, ContinuousLinearMap.comp_assoc]
  exact norm_comp_left_contraction (𝕜 := 𝕜) (X := X)
    (Y := C(Set.Icc c.val.1 c.val.2, 𝕜)) (Z := IntervalContinuous 𝕜)
    (continuousMapPullback ⟨e, e.continuous⟩)
    (norm_continuousMapPullback_le (𝕜 := 𝕜) ⟨e, e.continuous⟩) _

theorem interval_backward_retraction {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p = ∞ ∨ 1 < p.toReal)
    (T : lp (fun _ : ℕ => X) p →L[𝕜] IntervalContinuous 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ (e : ℕ ↪ ℕ) (c : NondegenerateUnitSubinterval),
      ‖((intervalRead c).comp T).comp (lpExtend p e)‖ ≤ ε := by
  obtain ⟨e, a, b, hab, hsmall⟩ := interval_lp_backward_reduction hp T hε
  refine ⟨e, ⟨(a,b), hab⟩, ?_⟩
  rw [ContinuousLinearMap.comp_assoc]
  exact (norm_intervalRead_comp_le ⟨(a,b), hab⟩ (T.comp (lpExtend p e))).trans hsmall

end ThesisCommon
