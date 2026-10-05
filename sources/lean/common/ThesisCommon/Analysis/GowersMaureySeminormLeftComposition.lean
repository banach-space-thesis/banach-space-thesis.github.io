import ThesisCommon.Analysis.GowersMaureyEndomorphismSeminorm

/-! Left composition by an arbitrary bounded operator preserves the actual
zero-seminorm kernel. The quantitative bound uses the ordinary norm of the
left factor and requires no approximation or multiplication theorem. -/
noncomputable section
open Filter
namespace ThesisCommon
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem operatorSequenceSeminorm_comp_le (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (S : E →L[𝕜] F) (T : F →L[𝕜] G) :
    operatorSequenceSeminorm x hx (T.comp S) ≤ ‖T‖ * operatorSequenceSeminorm x hx S := by
  change limsup (fun n => ‖T (S (x n))‖) atTop ≤
    ‖T‖ * limsup (fun n => ‖S (x n)‖) atTop
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖T‖ * ‖S (x n)‖) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n =>
      mul_le_mul_of_nonneg_left (operator_sequence_norm_le x hx S n) (norm_nonneg T)))
  have hm : Monotone (fun r : ℝ => ‖T‖ * r) :=
    fun _ _ h => mul_le_mul_of_nonneg_left h (norm_nonneg T)
  have heq := hm.map_limsup_of_continuousAt (fun n => ‖S (x n)‖)
    (continuous_const.mul continuous_id).continuousAt
    (operator_sequence_boundedAbove x hx S) (operator_sequence_cobounded x S)
  apply (limsup_le_limsup (Eventually.of_forall (fun n => T.le_opNorm (S (x n))))
    (operator_sequence_cobounded x (T.comp S)) hb).trans
  exact heq.symm.le

end ThesisCommon
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem spaceOperatorSeminorm_comp_le_opNorm (D : ConstructionData 𝕜)
    (T S : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D (T.comp S) ≤ ‖T‖ * spaceOperatorSeminorm D S := by
  rw [spaceOperatorSeminorm_apply]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  have hx : ∀ n, ‖denseEmbedding D (u.vector n)‖ ≤ 1 :=
    u.norm_inSubspace_le_one
  apply (operatorSequenceSeminorm_comp_le (fun n => denseEmbedding D (u.vector n)) hx S T).trans
  exact mul_le_mul_of_nonneg_left (u.limsup_le_spaceOperatorSeminorm S) (norm_nonneg T)

theorem spaceOperatorSeminorm_comp_eq_zero_of_right (D : ConstructionData 𝕜)
    (T S : ShiftSpace D →L[𝕜] ShiftSpace D) (hS : spaceOperatorSeminorm D S = 0) :
    spaceOperatorSeminorm D (T.comp S) = 0 := by
  apply le_antisymm _ (apply_nonneg (spaceOperatorSeminorm D) _)
  simpa only [hS, mul_zero] using spaceOperatorSeminorm_comp_le_opNorm D T S

end ThesisCommon.GowersMaurey
