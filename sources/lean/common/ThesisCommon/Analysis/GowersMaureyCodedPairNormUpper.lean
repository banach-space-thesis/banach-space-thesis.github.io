import ThesisCommon.Analysis.GowersMaureyScaledSpecialBounds
import ThesisCommon.Analysis.GowersMaureyOneExceptionRIS

/-! The genuine upper bound for the coded detecting family. All form
tests of the constructed implicit norm are controlled, including the
exceptional size and arbitrary spread/interval images. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ}

theorem CodedDetectingFamily.contracted_sum_norm_le {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) codedPairGrowthBudget) :
    implicitNorm D (∑ i, specialPairContraction T • (d.pair i).vector) ≤
      3*(D.j (2*t) : ℝ)/logarithmicWeight (D.j (2*t)) := by
  obtain ⟨h⟩ := d.contracted_outerRIS (D.j_positive _)
  have hb := h.sum_norm_le_one_exception_interpolation (D.j (2*t))
    (by norm_num : (1/4 : ℝ) < 1) (specialPairContraction_exception_budget T)
    (fun z hz m n E F => d.scaled_special_affine_exception_bound hz
      (specialPairContraction_pos T).le E F m n)
  rw [D.interpolationG_omit_size t] at hb
  norm_num only at hb
  simpa only [mul_div_assoc] using hb

theorem CodedDetectingFamily.sum_norm_le {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) codedPairGrowthBudget) :
    implicitNorm D (∑ i, (d.pair i).vector) ≤
      (3/specialPairContraction T)*(D.j (2*t) : ℝ)/logarithmicWeight (D.j (2*t)) := by
  have hb := d.contracted_sum_norm_le
  rw [← Finset.smul_sum, seminorm_real_smul, abs_of_pos (specialPairContraction_pos T)] at hb
  calc
    _ ≤ (3*(D.j (2*t) : ℝ)/logarithmicWeight (D.j (2*t)))/specialPairContraction T :=
      (le_div_iff₀ (specialPairContraction_pos T)).mpr (by simpa only [mul_comm] using hb)
    _ = _ := by ring

end ThesisCommon.GowersMaurey
