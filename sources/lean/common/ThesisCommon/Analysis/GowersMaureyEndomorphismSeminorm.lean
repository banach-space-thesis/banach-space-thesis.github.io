import ThesisCommon.Analysis.GowersMaureyOperatorSeminorm

/-! The actual block-sequence seminorm on endomorphisms of the completed
shift space. Restriction to the top subspace only removes a subtype from
the source's general subspace definition. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
set_option synthInstance.maxHeartbeats 100000
variable {𝕜 : Type*} [RCLike 𝕜]

def restrictOperatorToTop (D : ConstructionData 𝕜) :
    (ShiftSpace D →L[𝕜] ShiftSpace D) →ₗ[𝕜]
      ((⊤ : Submodule 𝕜 (ShiftSpace D)) →L[𝕜] ShiftSpace D) where
  toFun T := T.comp (⊤ : Submodule 𝕜 (ShiftSpace D)).subtypeL
  map_add' S T := by ext x; rfl
  map_smul' c T := by ext x; rfl

def spaceOperatorSeminorm (D : ConstructionData 𝕜) :
    Seminorm 𝕜 (ShiftSpace D →L[𝕜] ShiftSpace D) :=
  (blockOperatorSeminorm D ⊤).comp (restrictOperatorToTop D)

theorem spaceOperatorSeminorm_apply (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    spaceOperatorSeminorm D T = sSup (Set.range (fun u : BlockTestSequence D ⊤ =>
      limsup (fun n => ‖T (denseEmbedding D (u.vector n))‖) atTop)) :=
  blockOperatorSeminorm_apply D ⊤ (restrictOperatorToTop D T)

theorem spaceOperatorSeminorm_le_norm (D : ConstructionData 𝕜)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) : spaceOperatorSeminorm D T ≤ ‖T‖ := by
  change blockOperatorSeminorm D ⊤ (T.comp (⊤ : Submodule 𝕜 (ShiftSpace D)).subtypeL) ≤ ‖T‖
  apply (blockOperatorSeminorm_le_norm D ⊤ _).trans
  apply (T.opNorm_comp_le _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Submodule.norm_subtypeL_le (⊤ : Submodule 𝕜 (ShiftSpace D))) (norm_nonneg T)

theorem spaceOperatorSeminorm_continuous (D : ConstructionData 𝕜) :
    Continuous (spaceOperatorSeminorm D) := by
  apply Seminorm.continuous_of_le (q := normSeminorm 𝕜 (ShiftSpace D →L[𝕜] ShiftSpace D))
    (@continuous_norm (ShiftSpace D →L[𝕜] ShiftSpace D) _)
  exact spaceOperatorSeminorm_le_norm D

theorem BlockTestSequence.limsup_le_spaceOperatorSeminorm
    {D : ConstructionData 𝕜} (u : BlockTestSequence D ⊤)
    (T : ShiftSpace D →L[𝕜] ShiftSpace D) :
    limsup (fun n => ‖T (denseEmbedding D (u.vector n))‖) atTop ≤ spaceOperatorSeminorm D T :=
  u.limsup_le_blockOperatorSeminorm (restrictOperatorToTop D T)

end ThesisCommon.GowersMaurey
