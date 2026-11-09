import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lusin (N) for Lipschitz maps in equal finite real dimensions

Hausdorff measure in the real dimension is an additive Haar measure. Its
Lipschitz image estimate, together with mutual absolute continuity of Haar
measures, proves the actual null-image statement needed before applying a
signed degree formula. This file does not assert that degree formula.
-/

namespace BanachIsometric

open MeasureTheory Set
open scoped NNReal ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The null-image conclusion holds for arbitrary sets, with no measurability
requirement on either the set or its image. Lipschitz regularity is needed only
on that set. The source and target measures may be different Haar measures. -/
theorem lipschitzOnWith_image_null_of_finrank_eq
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : E → F} {K : ℝ≥0} {S : Set E} (hf : LipschitzOnWith K f S)
    (hS : μ S = 0) : ν (f '' S) = 0 := by
  let HE : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  let HF : Measure F := Measure.hausdorffMeasure (Module.finrank ℝ F)
  have hHE : HE S = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure HE μ) hS
  have hbound : HF (f '' S) ≤
      (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * HE S := by
    change Measure.hausdorffMeasure (Module.finrank ℝ F) (f '' S) ≤ _
    rw [← hdim]
    exact hf.hausdorffMeasure_image_le (Nat.cast_nonneg _)
  have hHF : HF (f '' S) = 0 := by
    apply le_antisymm
    · simpa only [hHE, mul_zero] using hbound
    · exact bot_le
  exact (Measure.absolutelyContinuous_isAddHaarMeasure ν HF) hHF

theorem lipschitzOnWith_image_null_of_subset
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : E → F} {K : ℝ≥0} {D S : Set E} (hf : LipschitzOnWith K f D)
    (hSD : S ⊆ D) (hS : μ S = 0) : ν (f '' S) = 0 :=
  lipschitzOnWith_image_null_of_finrank_eq μ ν hdim (hf.mono hSD) hS

/-- The Lusin (N) property required in the paper's signed-area argument. -/
theorem lipschitzWith_sends_null_sets_to_null
    (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ S : Set E, μ S = 0 → ν (f '' S) = 0 :=
  fun _ hS ↦ lipschitzOnWith_image_null_of_finrank_eq μ ν hdim hf.lipschitzOnWith hS

end BanachIsometric
