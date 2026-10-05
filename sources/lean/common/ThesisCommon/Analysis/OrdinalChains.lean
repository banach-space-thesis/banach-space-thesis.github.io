import ThesisCommon.Analysis.OrdinalClosedCopies
import ThesisCommon.Analysis.SequenceBlockTailBounds

/-! Finite chains of actual closed ordinal copies. Prepending a closed
copy refines the range and preserves every earlier operator-norm estimate. -/
noncomputable section
universe u
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : Ordinal.{u}}

abbrev OrdinalChain (α : Ordinal.{u}) := List (OrdinalClosedCopy α α)

def ordinalChainRead : OrdinalChain α → (OrdinalContinuous 𝕜 α) →L[𝕜] (OrdinalContinuous 𝕜 α)
  | [] => ContinuousLinearMap.id 𝕜 _
  | c :: cs => (ordinalCopyRead c).comp (ordinalChainRead cs)

def ordinalChainInsert : OrdinalChain α → (OrdinalContinuous 𝕜 α) →L[𝕜] (OrdinalContinuous 𝕜 α)
  | [] => ContinuousLinearMap.id 𝕜 _
  | c :: cs => (ordinalChainInsert cs).comp (ordinalCopyInsert c)

theorem norm_ordinalChainRead_le (cs : OrdinalChain α) : ‖ordinalChainRead (𝕜 := 𝕜) cs‖ ≤ 1 := by
  induction cs with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons c cs ih =>
    exact (norm_comp_left_contraction (𝕜 := 𝕜)
      (X := (OrdinalContinuous 𝕜 α)) (Y := (OrdinalContinuous 𝕜 α)) (Z := (OrdinalContinuous 𝕜 α))
      (ordinalCopyRead (𝕜 := 𝕜) c) (norm_ordinalCopyRead_le (𝕜 := 𝕜) c)
      (ordinalChainRead (𝕜 := 𝕜) cs)).trans ih

theorem norm_ordinalChainInsert_le (cs : OrdinalChain α) : ‖ordinalChainInsert (𝕜 := 𝕜) cs‖ ≤ 1 := by
  induction cs with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons c cs ih =>
    exact (norm_comp_right_contraction (𝕜 := 𝕜)
      (X := (OrdinalContinuous 𝕜 α)) (Y := (OrdinalContinuous 𝕜 α)) (Z := (OrdinalContinuous 𝕜 α))
      (ordinalChainInsert (𝕜 := 𝕜) cs) (ordinalCopyInsert (𝕜 := 𝕜) c)
      (norm_ordinalCopyInsert_le (𝕜 := 𝕜) c)).trans ih

theorem ordinalChainRead_comp_insert (cs : OrdinalChain α) :
    (ordinalChainRead (𝕜 := 𝕜) cs).comp (ordinalChainInsert cs) = ContinuousLinearMap.id 𝕜 _ := by
  induction cs with
  | nil => simp [ordinalChainRead, ordinalChainInsert]
  | cons c cs ih =>
    simp only [ordinalChainRead, ordinalChainInsert, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (ordinalChainRead cs), ih, ContinuousLinearMap.id_comp,
      ordinalCopyRead_comp_insert]

theorem ordinalChainRead_append (a b : OrdinalChain α) :
    ordinalChainRead (𝕜 := 𝕜) (a ++ b) = (ordinalChainRead a).comp (ordinalChainRead b) := by
  induction a with
  | nil => simp [ordinalChainRead]
  | cons c a ih => simp [ordinalChainRead, ih, ContinuousLinearMap.comp_assoc]

def OrdinalChain.Refines (b a : OrdinalChain α) : Prop := ∃ c, b = c ++ a

theorem OrdinalChain.Refines.refl (a : OrdinalChain α) : a.Refines a := ⟨[], rfl⟩

theorem OrdinalChain.Refines.trans {a b c : OrdinalChain α}
    (hab : a.Refines b) (hbc : b.Refines c) : a.Refines c := by
  obtain ⟨l, rfl⟩ := hab
  obtain ⟨m, rfl⟩ := hbc
  exact ⟨l ++ m, (List.append_assoc ..).symm⟩

theorem norm_ordinalChainRead_comp_le_of_refines {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] (OrdinalContinuous 𝕜 α)) {a b : OrdinalChain α} (h : b.Refines a) :
    ‖(ordinalChainRead b).comp T‖ ≤ ‖(ordinalChainRead a).comp T‖ := by
  obtain ⟨c, rfl⟩ := h
  rw [ordinalChainRead_append, ContinuousLinearMap.comp_assoc]
  exact norm_comp_left_contraction _ (norm_ordinalChainRead_le (𝕜 := 𝕜) c) _

/-- The concrete embedding whose pullback is the chain's read operator. -/
def ordinalChainMap : OrdinalChain α → C((OrdinalInterval α), (OrdinalInterval α))
  | [] => ContinuousMap.id _
  | c :: cs => (ordinalChainMap cs).comp c.val

theorem ordinalChainRead_apply (cs : OrdinalChain α) (f : (OrdinalContinuous 𝕜 α)) (t : (OrdinalInterval α)) :
    ordinalChainRead cs f t = f (ordinalChainMap cs t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih =>
    change ordinalChainRead cs f (c.val t) = _
    exact ih _

theorem ordinalChainMap_injective (cs : OrdinalChain α) : Function.Injective (ordinalChainMap cs) := by
  induction cs with
  | nil => exact Function.injective_id
  | cons c cs ih =>
    exact ih.comp c.property

theorem ordinalChainMap_closed_copy (cs : OrdinalChain α) :
    IsClosed (Set.range (ordinalChainMap cs)) ∧
      Nonempty ((OrdinalInterval α) ≃ₜ Set.range (ordinalChainMap cs)) := by
  have h := (ordinalChainMap cs).continuous.isClosedEmbedding (ordinalChainMap_injective cs)
  exact ⟨h.isClosed_range, ⟨h.isEmbedding.toHomeomorph⟩⟩

theorem ordinalChainMap_append (a b : OrdinalChain α) (t : (OrdinalInterval α)) :
    ordinalChainMap (a ++ b) t = ordinalChainMap b (ordinalChainMap a t) := by
  induction a generalizing t with
  | nil => rfl
  | cons c a ih =>
    exact ih (c.val t)

theorem OrdinalChain.Refines.range_subset {a b : OrdinalChain α} (h : b.Refines a) :
    Set.range (ordinalChainMap b) ⊆ Set.range (ordinalChainMap a) := by
  obtain ⟨c, rfl⟩ := h
  rintro t ⟨s, rfl⟩
  exact ⟨ordinalChainMap c s, (ordinalChainMap_append c a s).symm⟩

end ThesisCommon

