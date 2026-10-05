import PEMS.MainStatements
import PEMS.MeasureChecks

/-! The zero-domain case must be separated before using the norm-one witnesses
in Lemma 4.25. These are special cases, not proofs of the full Theorem 1.1. -/
noncomputable section
namespace PEMS
open ThesisCommon MeasureTheory
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem theorem_1_1_zero (μ : Measure X) (ν : Measure Y) :
    Theorem_1_1 μ ν (0 : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) := by
  intro _ _
  have hloc : localizedWeakNoncompactness (0 : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) = 0 := by
    have h := localizedWeakNoncompactness_bounds (0 : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν)
    exact le_antisymm (by simpa using h.2) h.1
  refine ⟨0, weaklyCompact_zero, ?_, ?_⟩
  · simpa using (weaklyCompact_zero (𝕜 := 𝕜) (E := LOne 𝕜 μ)
      (F := LOne 𝕜 ν)).weakEssentialNorm_eq_zero
  · simp [hloc]

theorem theorem_1_1_subsingleton_domain (μ : Measure X) (ν : Measure Y)
    [Subsingleton (LOne 𝕜 μ)] (T : LOne 𝕜 μ →L[𝕜] LOne 𝕜 ν) :
    Theorem_1_1 μ ν T := by
  have hT : T = 0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  rw [hT]
  exact theorem_1_1_zero μ ν

end PEMS
