import ThesisCommon.Analysis.FiniteRankCorrectionHomotopy
import ThesisCommon.Analysis.GowersMaureyStrictlySingularClosedRange

/-! Identity minus an actual strictly singular operator on the constructed
space has an invertible finite-rank correction. The homotopy is the actual
path I-tS, and every tail restriction comes from strict singularity. -/
noncomputable section
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem strictlySingular_hasFiniteRankInvertibleCorrection_id_sub
    (D : ConstructionData 𝕜) (S : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hS : IsStrictlySingularOperator S) :
    HasFiniteRankInvertibleCorrection (ContinuousLinearMap.id 𝕜 (ShiftSpace D)-S) := by
  let P : ℝ → ShiftSpace D →L[𝕜] ShiftSpace D :=
    fun t => ContinuousLinearMap.id 𝕜 (ShiftSpace D)-(t : 𝕜) • S
  have hP : Continuous P :=
    continuous_const.sub (RCLike.continuous_ofReal.smul continuous_const)
  have hlower : ∀ t, ∃ E : Submodule 𝕜 (ShiftSpace D), IsClosed (E : Set (ShiftSpace D)) ∧
      FiniteDimensional 𝕜 (ShiftSpace D ⧸ E) ∧ ∃ c : ℝ, 0<c ∧
      ∀ x : E, c*‖x.val‖ ≤ ‖P t x.val‖ := by
    intro t
    exact strictlySingular_id_sub_smul_finiteCodimensional_lower_bound D S hS (t : 𝕜)
  have hzero : IsUnit (P 0) := by
    dsimp only [P]
    rw [RCLike.ofReal_zero,zero_smul,sub_zero]
    exact isUnit_one
  have h := finiteRankInvertibleCorrection_of_connected_family P hP hlower 0 hzero 1
  simpa only [P, RCLike.ofReal_one, one_smul] using h

theorem strictlySingular_hasFiniteRankInvertibleCorrection_id_sub_smul
    (D : ConstructionData 𝕜) (S : ShiftSpace D →L[𝕜] ShiftSpace D)
    (hS : IsStrictlySingularOperator S) (t : 𝕜) :
    HasFiniteRankInvertibleCorrection (ContinuousLinearMap.id 𝕜 (ShiftSpace D)-t • S) :=
  strictlySingular_hasFiniteRankInvertibleCorrection_id_sub D (t • S) (hS.smul t)

end ThesisCommon.GowersMaurey
