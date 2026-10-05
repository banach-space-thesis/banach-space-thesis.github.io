import ThesisCommon.Analysis.GowersMaureySpecialHighBounds
import ThesisCommon.Analysis.GowersMaureyRISContractions

/-! A fixed positive contraction of the selected pairs leaves a strict
margin for the exceptional special tests in the actual norm envelope. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]
variable {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
variable {T : Y →L[𝕜] ShiftSpace D} {ε η : ℝ} {G : C00 𝕜 → ℝ}

def specialPairContraction (T : Y →L[𝕜] ShiftSpace D) : ℝ := 1/(64*(1+‖T‖))

theorem specialPairContraction_pos (T : Y →L[𝕜] ShiftSpace D) :
    0 < specialPairContraction T := by unfold specialPairContraction; positivity

theorem specialPairContraction_eight_le_one (T : Y →L[𝕜] ShiftSpace D) :
    8*specialPairContraction T ≤ 1 := by
  unfold specialPairContraction
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  linarith [norm_nonneg T]

theorem specialPairContraction_exception_budget (T : Y →L[𝕜] ShiftSpace D) :
    specialPairContraction T*(‖T‖+24) < 1-(1/4 : ℝ) := by
  unfold specialPairContraction
  rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
  linarith [norm_nonneg T]

theorem CodedDetectingFamily.scaled_special_affine_exception_bound {t : ℕ}
    (d : CodedDetectingFamily T ε η (D.j (2*t)-1) (D.j (2*t)) G)
    {g : Fin (D.j (2*t)) → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    {r : ℝ} (hr : 0 ≤ r) (E F : Interval) (m n : ℕ) :
    ‖pairing (specialFunctional g) (restrict E (spread m n
      (restrict F (∑ i, r • (d.pair i).vector))))‖ ≤
      r*(‖T‖+24)+(1/4 : ℝ)*implicitNorm D (restrict F (∑ i, r • (d.pair i).vector)) := by
  rw [← Finset.smul_sum]
  simp only [restrict_real_smul, (spread m n).map_smul_of_tower,
    (pairing (specialFunctional g)).map_smul_of_tower, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr, seminorm_real_smul]
  have h := mul_le_mul_of_nonneg_left (d.special_affine_exception_bound hg E F m n) hr
  nlinarith only [h]

theorem CodedDetectingFamily.contracted_outerRIS {k : ℕ} (hk : 0 < k)
    (d : CodedDetectingFamily T ε η (k-1) k codedPairGrowthBudget) :
    IsRIS D 1 (fun i => specialPairContraction T • (d.pair i).vector) := by
  have h := (d.outerRIS hk).real_smul
    (mul_pos (by norm_num : (0 : ℝ) < 8) (specialPairContraction_pos T))
    (specialPairContraction_eight_le_one T)
  simpa only [smul_smul, mul_assoc, show (8 : ℝ)*(1/8)=1 by norm_num,
    show ∀ r : ℝ, 8*r*(1/8)=r by intro r; ring] using h

end ThesisCommon.GowersMaurey
