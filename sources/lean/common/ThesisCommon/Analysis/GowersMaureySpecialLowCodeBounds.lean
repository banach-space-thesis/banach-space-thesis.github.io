import ThesisCommon.Analysis.GowersMaureySpecialCollisions
import ThesisCommon.Analysis.GowersMaureyLowCodeBudget
import ThesisCommon.Analysis.GowersMaureyNormingForms
import ThesisCommon.Analysis.GowersMaureyCompletedPairing

/-! The genuinely small part of a competing special functional. Arbitrary
injective coding permits low recursive sizes; their actual number bounds
this part by one quarter of the norm. No monotonicity of competing codes
is assumed. -/
noncomputable section
open scoped BigOperators
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

def specialLowFunctional (D : ConstructionData 𝕜) {k : ℕ}
    (g : Fin k → C00 𝕜) (t : ℕ) : C00 𝕜 :=
  (Real.sqrt (logarithmicWeight k))⁻¹ •
    ∑ i ∈ Finset.univ.filter (fun i => specialSequenceSize D g i ≤ D.j (2*t)), g i

def specialHighFunctional (D : ConstructionData 𝕜) {k : ℕ}
    (g : Fin k → C00 𝕜) (t : ℕ) : C00 𝕜 :=
  specialFunctional g - specialLowFunctional D g t

theorem SpecialSequence.lowFunctional_bound {D : ConstructionData 𝕜}
    {k : ℕ} {g : Fin k → C00 𝕜} (hg : SpecialSequence D (implicitNorm D) g)
    (t : ℕ) (x : ShiftSpace D) :
    ‖completedPairing D (specialLowFunctional D g t) x‖ ≤
      ((t : ℝ)+1)/Real.sqrt (logarithmicWeight k) * ‖x‖ := by
  classical
  have hsm (r : ℝ) (a : C00 𝕜) : r • a = (r : 𝕜) • a := by
    ext n
    simp only [Finsupp.smul_apply,smul_eq_mul,RCLike.real_smul_eq_coe_mul]
  rw [specialLowFunctional,hsm,map_smul,map_sum]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,
    norm_mul,RCLike.norm_ofReal,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hc : ((Finset.univ.filter (fun i => specialSequenceSize D g i ≤ D.j (2*t))).card : ℝ) ≤
      (t : ℝ)+1 := by exact_mod_cast hg.size_le_selected_count t
  calc
    _ ≤ (Real.sqrt (logarithmicWeight k))⁻¹ *
        ∑ _i ∈ Finset.univ.filter (fun i => specialSequenceSize D g i ≤ D.j (2*t)), ‖x‖ :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum
        (fun i _ => completedPairing_norm_bound (hg.size_averaged i).dualUnit x)))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt (logarithmicWeight k))⁻¹ * (((t : ℝ)+1)*‖x‖) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (norm_nonneg x))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by ring

theorem SpecialSequence.lowFunctional_le_quarter {D : ConstructionData 𝕜}
    {t : ℕ} {g : Fin (D.j (2*t)) → C00 𝕜}
    (hg : SpecialSequence D (implicitNorm D) g) (x : ShiftSpace D) :
    ‖completedPairing D (specialLowFunctional D g t) x‖ ≤ (1/4 : ℝ)*‖x‖ := by
  apply (hg.lowFunctional_bound t x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  exact (div_le_div_of_nonneg_right (by linarith : (t : ℝ)+1 ≤ (t : ℝ)+3)
    (Real.sqrt_nonneg _)).trans (D.low_code_count_div_sqrt_weight_le t)

theorem SpecialSequence.highFunctional_le_five_quarters {D : ConstructionData 𝕜}
    {t : ℕ} {g : Fin (D.j (2*t)) → C00 𝕜}
    (hg : SpecialSequence D (implicitNorm D) g) (x : ShiftSpace D) :
    ‖completedPairing D (specialHighFunctional D g t) x‖ ≤ (5/4 : ℝ)*‖x‖ := by
  rw [specialHighFunctional,map_sub,ContinuousLinearMap.sub_apply]
  have hs := completedPairing_norm_bound (hg.specialFunctional_dualUnit D ⟨t,rfl⟩) x
  have hl := hg.lowFunctional_le_quarter x
  exact (norm_sub_le _ _).trans (by linarith)

theorem SpecialSequence.lowFunctional_restrict_spread_bound {D : ConstructionData 𝕜}
    {t : ℕ} {g : Fin (D.j (2*t)) → C00 𝕜}
    (hg : SpecialSequence D (implicitNorm D) g) (E : Interval) (m n : ℕ) (x : C00 𝕜) :
    ‖pairing (specialLowFunctional D g t) (restrict E (spread m n x))‖ ≤
      (1/4 : ℝ)*implicitNorm D x := by
  have h := hg.lowFunctional_le_quarter (denseEmbedding D (restrict E (spread m n x)))
  rw [completedPairing_denseEmbedding,denseEmbedding_norm] at h
  apply h.trans
  exact mul_le_mul_of_nonneg_left
    ((implicitNorm_restrict_le D E _).trans (implicitNorm_spread_le D m n x)) (by norm_num)

end ThesisCommon.GowersMaurey
