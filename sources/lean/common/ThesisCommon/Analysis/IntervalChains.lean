import ThesisCommon.Analysis.IntervalRetractions

/-! Finite nested interval restrictions. Each list records actual closed
interval restrictions, normalized by their affine homeomorphisms. Prepending
an interval refines the copy and preserves every earlier norm estimate. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev IntervalChain := List NondegenerateUnitSubinterval

def intervalChainRead : IntervalChain → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜
  | [] => ContinuousLinearMap.id 𝕜 _
  | c :: cs => (intervalRead c).comp (intervalChainRead cs)

def intervalChainInsert : IntervalChain → IntervalContinuous 𝕜 →L[𝕜] IntervalContinuous 𝕜
  | [] => ContinuousLinearMap.id 𝕜 _
  | c :: cs => (intervalChainInsert cs).comp (intervalInsert c)

theorem norm_intervalChainRead_le (cs : IntervalChain) : ‖intervalChainRead (𝕜 := 𝕜) cs‖ ≤ 1 := by
  induction cs with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons c cs ih =>
    exact (norm_comp_left_contraction (𝕜 := 𝕜)
      (X := IntervalContinuous 𝕜) (Y := IntervalContinuous 𝕜) (Z := IntervalContinuous 𝕜)
      (intervalRead (𝕜 := 𝕜) c) (norm_intervalRead_le (𝕜 := 𝕜) c)
      (intervalChainRead (𝕜 := 𝕜) cs)).trans ih

theorem norm_intervalChainInsert_le (cs : IntervalChain) : ‖intervalChainInsert (𝕜 := 𝕜) cs‖ ≤ 1 := by
  induction cs with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons c cs ih =>
    exact (norm_comp_right_contraction (𝕜 := 𝕜)
      (X := IntervalContinuous 𝕜) (Y := IntervalContinuous 𝕜) (Z := IntervalContinuous 𝕜)
      (intervalChainInsert (𝕜 := 𝕜) cs) (intervalInsert (𝕜 := 𝕜) c)
      (norm_intervalInsert_le (𝕜 := 𝕜) c)).trans ih

theorem intervalChainRead_comp_insert (cs : IntervalChain) :
    (intervalChainRead (𝕜 := 𝕜) cs).comp (intervalChainInsert cs) = ContinuousLinearMap.id 𝕜 _ := by
  induction cs with
  | nil => simp [intervalChainRead, intervalChainInsert]
  | cons c cs ih =>
    simp only [intervalChainRead, intervalChainInsert, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (intervalChainRead cs), ih, ContinuousLinearMap.id_comp,
      intervalRead_comp_insert]

theorem intervalChainRead_append (a b : IntervalChain) :
    intervalChainRead (𝕜 := 𝕜) (a ++ b) = (intervalChainRead a).comp (intervalChainRead b) := by
  induction a with
  | nil => simp [intervalChainRead]
  | cons c a ih => simp [intervalChainRead, ih, ContinuousLinearMap.comp_assoc]

def IntervalChain.Refines (b a : IntervalChain) : Prop := ∃ c, b = c ++ a

theorem IntervalChain.Refines.refl (a : IntervalChain) : a.Refines a := ⟨[], rfl⟩

theorem IntervalChain.Refines.trans {a b c : IntervalChain}
    (hab : a.Refines b) (hbc : b.Refines c) : a.Refines c := by
  obtain ⟨l, rfl⟩ := hab
  obtain ⟨m, rfl⟩ := hbc
  exact ⟨l ++ m, (List.append_assoc ..).symm⟩

theorem norm_intervalChainRead_comp_le_of_refines {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : X →L[𝕜] IntervalContinuous 𝕜) {a b : IntervalChain} (h : b.Refines a) :
    ‖(intervalChainRead b).comp T‖ ≤ ‖(intervalChainRead a).comp T‖ := by
  obtain ⟨c, rfl⟩ := h
  rw [intervalChainRead_append, ContinuousLinearMap.comp_assoc]
  exact norm_comp_left_contraction _ (norm_intervalChainRead_le (𝕜 := 𝕜) c) _

/-- The concrete embedding whose pullback is the chain's read operator. -/
def intervalChainMap : IntervalChain → C(UnitInterval, UnitInterval)
  | [] => ContinuousMap.id _
  | c :: cs => (intervalChainMap cs).comp
      ⟨fun t => (unitSubintervalHomeomorph c.val.1 c.val.2 c.property t).val,
        continuous_subtype_val.comp (unitSubintervalHomeomorph c.val.1 c.val.2 c.property).continuous⟩

theorem intervalChainRead_apply (cs : IntervalChain) (f : IntervalContinuous 𝕜) (t : UnitInterval) :
    intervalChainRead cs f t = f (intervalChainMap cs t) := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih =>
    change intervalChainRead cs f ((unitSubintervalHomeomorph c.val.1 c.val.2 c.property t).val) = _
    exact ih _

theorem intervalChainMap_injective (cs : IntervalChain) : Function.Injective (intervalChainMap cs) := by
  induction cs with
  | nil => exact Function.injective_id
  | cons c cs ih =>
    exact ih.comp (Subtype.val_injective.comp
      (unitSubintervalHomeomorph c.val.1 c.val.2 c.property).injective)

theorem intervalChainMap_closed_copy (cs : IntervalChain) :
    IsClosed (Set.range (intervalChainMap cs)) ∧
      Nonempty (UnitInterval ≃ₜ Set.range (intervalChainMap cs)) := by
  have h := (intervalChainMap cs).continuous.isClosedEmbedding (intervalChainMap_injective cs)
  exact ⟨h.isClosed_range, ⟨h.isEmbedding.toHomeomorph⟩⟩

theorem intervalChainMap_append (a b : IntervalChain) (t : UnitInterval) :
    intervalChainMap (a ++ b) t = intervalChainMap b (intervalChainMap a t) := by
  induction a generalizing t with
  | nil => rfl
  | cons c a ih =>
    exact ih ((unitSubintervalHomeomorph c.val.1 c.val.2 c.property t).val)

theorem IntervalChain.Refines.range_subset {a b : IntervalChain} (h : b.Refines a) :
    Set.range (intervalChainMap b) ⊆ Set.range (intervalChainMap a) := by
  obtain ⟨c, rfl⟩ := h
  rintro t ⟨s, rfl⟩
  exact ⟨intervalChainMap c s, (intervalChainMap_append c a s).symm⟩

end ThesisCommon
