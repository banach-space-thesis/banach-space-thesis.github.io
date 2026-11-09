import PL1.MatrixSmoothing

/-! # An operator property preserved by bounded composition

The quantified pre- and post-compositions are actual bounded linear maps
to and from the reviewed interval L1 space. The definition does not assert
that any particular operator has this property.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace PL1

variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def HasVanishingDyadicTrace (S : X →L[𝕜] Y) : Prop :=
  ∀ (A : Y →L[𝕜] IntervalL1 𝕜) (B : IntervalL1 𝕜 →L[𝕜] X),
    Tendsto (fun n => DyadicTrace.trace n (A.comp (S.comp B))) atTop (𝓝 0)

namespace HasVanishingDyadicTrace

theorem comp_left {S : X →L[𝕜] Y} (hS : HasVanishingDyadicTrace S)
    (T : Y →L[𝕜] Z) : HasVanishingDyadicTrace (T.comp S) := by
  intro A B
  simpa only [ContinuousLinearMap.comp_assoc] using hS (A.comp T) B

theorem comp_right {S : Y →L[𝕜] Z} (hS : HasVanishingDyadicTrace S)
    (T : X →L[𝕜] Y) : HasVanishingDyadicTrace (S.comp T) := by
  intro A B
  simpa only [ContinuousLinearMap.comp_assoc] using hS A (T.comp B)

theorem smul {S : X →L[𝕜] Y} (hS : HasVanishingDyadicTrace S) (c : 𝕜) :
    HasVanishingDyadicTrace (c • S) := by
  intro A B
  have he : A.comp ((c • S).comp B) = (c • A).comp (S.comp B) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  rw [he]
  exact hS (c • A) B

theorem one_le_norm_id_sub {S : X →L[𝕜] Y} (hS : HasVanishingDyadicTrace S)
    (A : Y →L[𝕜] IntervalL1 𝕜) (B : IntervalL1 𝕜 →L[𝕜] X) :
    1 ≤ ‖DyadicTrace.restrictLinfty
      (ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) - A.comp (S.comp B))‖ :=
  DyadicTrace.one_le_norm_id_sub _ (hS A B)

theorem not_factors_identity {S : X →L[𝕜] Y} (hS : HasVanishingDyadicTrace S)
    (A : Y →L[𝕜] IntervalL1 𝕜) (B : IntervalL1 𝕜 →L[𝕜] X) :
    A.comp (S.comp B) ≠ ContinuousLinearMap.id 𝕜 (IntervalL1 𝕜) := by
  intro he
  have hn := hS.one_le_norm_id_sub A B
  rw [he, sub_self] at hn
  simp only [DyadicTrace.restrictLinfty, ContinuousLinearMap.zero_comp, norm_zero] at hn
  norm_num at hn

end HasVanishingDyadicTrace

end PL1
