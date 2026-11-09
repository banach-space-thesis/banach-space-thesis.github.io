import SurveyStatements.P5OperatorReductionOuterShadowTrace

/-! The unnormalized inner slice trace on the actual dyadic algebra.
All measure bounds, finite additivity, and set invariance follow from
the full sequence of genuine Haar level traces. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Classical BigOperators Topology
namespace SurveyStatements.P5OperatorReduction
open SurveyStatements.P5 SurveyStatements.P5Support SurveyStatements.P5L1Variation
variable {𝕜 : Type*} [RCLike 𝕜]

def innerSliceDyadicTraceValue (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (i : LpHaarDyadicSetIndex) : 𝕜 :=
  ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i) : 𝕜) *
    localTraceFunctional 𝕜 i.1 i.2 (meanZeroInnerSlice T f η hη hb)

theorem norm_innerSliceDyadicTraceValue_le (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (i : LpHaarDyadicSetIndex) :
    ‖innerSliceDyadicTraceValue p T f η hη hb i‖ ≤
      (‖T‖ * ‖f‖) * (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarDyadicSet i) := by
  rw [innerSliceDyadicTraceValue, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg measureReal_nonneg, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (norm_innerSliceLocalTrace_le p T f η hη hb i.1 i.2) measureReal_nonneg

theorem innerSliceDyadicTraceValue_full_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (i : LpHaarDyadicSetIndex) :
    Tendsto (fun n => lpHaarLevelTrace
      (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (meanZeroInnerSlice T f η hη hb))) n
        (lpHaarDyadicSet i)) atTop
      (𝓝 (innerSliceDyadicTraceValue p T f η hη hb i)) := by
  obtain ⟨r, S⟩ := i
  by_cases hS : S.Nonempty
  · have hmass : 0 < (volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) := by
      rw [lpHaarBlockParent_real_measure]
      exact mul_pos (by exact_mod_cast Finset.card_pos.mpr hS)
        (intervalLpDyadicRadius_pos r)
    have hmass𝕜 : ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr hmass.ne'
    have hformula (j : ℕ) :
        lpHaarLevelTrace
          (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (meanZeroInnerSlice T f η hη hb)))
          (r + j) (lpHaarBlockParent r S) =
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜) *
          equalDyadicLevelAverage 𝕜 (meanZeroInnerSlice T f η hη hb) r S j := by
      rw [equalDyadicLevelAverage_eq_normalized_trace 𝕜
        (meanZeroInnerSlice T f η hη hb) r S hS j,
        ← mul_assoc, mul_inv_cancel₀ hmass𝕜, one_mul]
    apply (tendsto_add_atTop_iff_nat r).mp
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜))
        atTop (𝓝 ((volume.restrict (Set.Icc (0 : ℝ) 1)).real (lpHaarBlockParent r S) : 𝕜))).mul
      (localTraceFunctional_tendsto 𝕜 (meanZeroInnerSlice T f η hη hb) r S)
    simpa only [innerSliceDyadicTraceValue, lpHaarDyadicSet, Nat.add_comm,
      hformula] using h
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simpa [innerSliceDyadicTraceValue, lpHaarDyadicSet, lpHaarBlockParent,
      lpHaarLevelTrace] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : 𝕜)) atTop (𝓝 0))

theorem innerSliceDyadicTraceValue_equal_sets (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (i j : LpHaarDyadicSetIndex) (hij : lpHaarDyadicSet i = lpHaarDyadicSet j) :
    innerSliceDyadicTraceValue p T f η hη hb i =
      innerSliceDyadicTraceValue p T f η hη hb j := by
  apply tendsto_nhds_unique (innerSliceDyadicTraceValue_full_tendsto p T f η hη hb i)
  simpa only [hij] using innerSliceDyadicTraceValue_full_tendsto p T f η hη hb j

theorem innerSliceDyadicTraceValue_additive (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (i j k : LpHaarDyadicSetIndex)
    (hij : Disjoint (lpHaarDyadicSet i) (lpHaarDyadicSet j))
    (hk : lpHaarDyadicSet k = lpHaarDyadicSet i ∪ lpHaarDyadicSet j) :
    innerSliceDyadicTraceValue p T f η hη hb k =
      innerSliceDyadicTraceValue p T f η hη hb i +
        innerSliceDyadicTraceValue p T f η hη hb j := by
  apply tendsto_nhds_unique (innerSliceDyadicTraceValue_full_tendsto p T f η hη hb k)
  have h := (innerSliceDyadicTraceValue_full_tendsto p T f η hη hb i).add
    (innerSliceDyadicTraceValue_full_tendsto p T f η hη hb j)
  convert h using 1
  funext n
  rw [hk, lpHaarLevelTrace_union _ n _ _
    (lpHaarDyadicSet_measurable i) (lpHaarDyadicSet_measurable j) hij]

theorem innerSliceDyadicTraceValue_reservoir_tendsto (p : BanachExponent)
    (T : MixedNorm 𝕜 p.val →L[𝕜] MixedNorm 𝕜 p.val)
    (f : Lp 𝕜 p.val (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (η : ℝ → 𝕜) (hη : StronglyMeasurable η) (hb : ∀ x, ‖η x‖ ≤ 1)
    (i : LpHaarDyadicSetIndex) (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    Tendsto (fun n => lpHaarLevelTrace
      (haarOperatorDiagonal 𝕜 (extendMeanZero 𝕜 (meanZeroInnerSlice T f η hη hb)))
      (σ n) (lpHaarDyadicSet i)) atTop
      (𝓝 (innerSliceDyadicTraceValue p T f η hη hb i)) :=
  (innerSliceDyadicTraceValue_full_tendsto p T f η hη hb i).comp hσ

end SurveyStatements.P5OperatorReduction
