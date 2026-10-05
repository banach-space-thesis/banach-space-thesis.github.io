import ThesisCommon.Analysis.OrdinalBakerOrder
import ThesisCommon.Analysis.OrdinalBakerPowers

/-! Finite closed covers of positive ordinal powers contain the entire
homeomorphism type of the interval in one member. The proof computes the
derivative rank, selects a cover member with the same last derivative, and
uses its increasing ordinal model. -/
noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinal_power_le_compact_model {A : Set Ordinal.{u}} {α β : Ordinal.{u}}
    (e : OrdinalInterval β ≃ₜ A) (hα : α ≠ 0)
    (hne : (ordinalDerived A α).Nonempty) : Ordinal.omega0 ^ α ≤ β := by
  let f : OrdinalInterval β → Ordinal.{u} := fun x => (e x).val
  have hf : IsClosedEmbedding f := (continuous_subtype_val.comp e.continuous).isClosedEmbedding
    (Subtype.val_injective.comp e.injective)
  have hfrange : range f = A := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      change (e (e.symm ⟨x, hx⟩)).val = x
      rw [e.apply_symm_apply]
  have heq := ordinalDerived_image_closedEmbedding hf univ α
  rw [image_univ, hfrange] at heq
  rw [heq] at hne
  have hdom : (ordinalDerived (univ : Set (OrdinalInterval β)) α).Nonempty :=
    image_nonempty.mp hne
  have hi := ordinalDerived_image_closedEmbedding
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{u}) β)).isClosedEmbedding_subtypeVal univ α
  rw [image_univ, Subtype.range_coe] at hi
  have hIcc : Icc (0 : Ordinal.{u}) β = Iic β := by ext x; simp
  have hi' : ordinalDerived (Iic β) α =
      (Subtype.val : OrdinalInterval β → Ordinal.{u}) ''
        ordinalDerived (univ : Set (OrdinalInterval β)) α := by
    calc
      ordinalDerived (Iic β) α = ordinalDerived (Icc (0 : Ordinal.{u}) β) α :=
        congrArg (fun S => ordinalDerived S α) hIcc.symm
      _ = _ := hi
  apply ordinal_power_le_of_nonempty_derivative hα
  rw [hi']
  exact hdom.image (Subtype.val : OrdinalInterval β → Ordinal.{u})

/-- For every positive ordinal exponent, one member of a finite closed cover
of [0,ω^α] is itself homeomorphic to the whole interval. -/
theorem ordinal_power_finite_closed_cover_homeomorph {ι : Type*} [Finite ι]
    {α : Ordinal.{u}} (hα : α ≠ 0) (A : ι → Set Ordinal.{u})
    (hA : ∀ i, IsClosed (A i))
    (hcover : Iic (Ordinal.omega0 ^ α) = ⋃ i, A i) :
    ∃ i, Nonempty (OrdinalInterval (Ordinal.omega0 ^ α) ≃ₜ A i) := by
  obtain ⟨i, hi⟩ := exists_ordinalDerived_eq_singleton_of_finite_cover A hA hcover α
    (ordinalDerived_Iic_power_self hα)
  have hDi : (ordinalDerived (A i) α).Nonempty := by rw [hi]; exact singleton_nonempty _
  have hsub : A i ⊆ Iic (Ordinal.omega0 ^ α) := by rw [hcover]; exact subset_iUnion A i
  have hcompact : IsCompact (A i) := by
    apply (isCompact_Icc : IsCompact (Icc (0 : Ordinal.{u}) (Ordinal.omega0 ^ α))).of_isClosed_subset (hA i)
    intro x hx
    exact ⟨bot_le, hsub hx⟩
  have hne : (A i).Nonempty := hDi.mono (by
    simpa using ordinalDerived_antitone (hA i) (show 0 ≤ α from bot_le))
  obtain ⟨β, e, _, hβ⟩ := ordinal_compact_order_homeomorph hcompact hne
  have hp : Ordinal.omega0 ^ α ≤ β := ordinal_power_le_compact_model e hα hDi
  have heq : β = Ordinal.omega0 ^ α := le_antisymm
    (hβ.trans (csSup_le hne hsub)) hp
  subst β
  exact ⟨i, ⟨e⟩⟩

/-- A directly usable closed copy for the operator reductions, with no
classification premise. Rank zero must be handled as the finite case. -/
theorem ordinal_power_finite_closed_cover {ι : Type*} [Finite ι]
    {α : Ordinal.{u}} (hα : α ≠ 0) (A : ι → Set Ordinal.{u})
    (hA : ∀ i, IsClosed (A i))
    (hcover : Iic (Ordinal.omega0 ^ α) = ⋃ i, A i) :
    ∃ i, ∃ f : OrdinalClosedCopy (Ordinal.omega0 ^ α) (Ordinal.omega0 ^ α),
      ∀ x, (f.val x).val ∈ A i := by
  obtain ⟨i, ⟨e⟩⟩ := ordinal_power_finite_closed_cover_homeomorph hα A hA hcover
  have hsub : A i ⊆ Iic (Ordinal.omega0 ^ α) := by rw [hcover]; exact subset_iUnion A i
  let g : C(OrdinalInterval (Ordinal.omega0 ^ α), OrdinalInterval (Ordinal.omega0 ^ α)) :=
    ⟨fun x => ⟨(e x).val, bot_le, hsub (e x).property⟩,
      (continuous_subtype_val.comp e.continuous).subtype_mk _⟩
  refine ⟨i, ⟨g, ?_⟩, ?_⟩
  · intro x y hxy
    apply e.injective
    exact Subtype.ext (congrArg
      (fun z : OrdinalInterval (Ordinal.omega0 ^ α) => z.val) hxy)
  · exact fun x => (e x).property

end ThesisCommon
