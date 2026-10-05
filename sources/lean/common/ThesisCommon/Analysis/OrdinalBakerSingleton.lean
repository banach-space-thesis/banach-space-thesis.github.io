import ThesisCommon.Analysis.OrdinalAbsorption
import ThesisCommon.Analysis.OrdinalCopiesClassification

/-! Baker's classification at characteristic (η,1), for every positive
ordinal η. A singleton last derivative places the increasing ordinal model
between ω^η and ω^η+ω^η; explicit short-tail absorption finishes. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinal_singleton_derivative_bounds {η β : Ordinal.{u}} (hη : η ≠ 0)
    (hne : (ordinalDerived (Iic β) η).Nonempty)
    (hsub : (ordinalDerived (Iic β) η).Subsingleton) :
    Ordinal.omega0 ^ η ≤ β ∧ β < Ordinal.omega0 ^ η + Ordinal.omega0 ^ η := by
  have hle := ordinal_power_le_of_nonempty_derivative hη hne
  refine ⟨hle, ?_⟩
  have hp : 0 < Ordinal.omega0 ^ η := Ordinal.opow_pos η Ordinal.omega0_pos
  have hmem : Ordinal.omega0 ^ η ∈ ordinalDerived (Iic β) η := by
    rw [ordinalDerived_Iic, ordinalDerived_univ, if_neg hη]
    exact ⟨⟨hp.ne', dvd_refl _⟩, hle⟩
  have hlt : Ordinal.omega0 ^ η < Ordinal.omega0 ^ η + Ordinal.omega0 ^ η := by
    simpa only [add_zero] using add_lt_add_left hp (Ordinal.omega0 ^ η)
  by_contra h
  have hmem' : Ordinal.omega0 ^ η + Ordinal.omega0 ^ η ∈ ordinalDerived (Iic β) η := by
    rw [ordinalDerived_Iic, ordinalDerived_univ, if_neg hη]
    exact ⟨⟨(hp.trans hlt).ne', (Ordinal.dvd_add_iff (dvd_refl _)).mpr (dvd_refl _)⟩,
      le_of_not_gt h⟩
  exact (ne_of_lt hlt) (hsub hmem hmem')

theorem ordinal_model_subsingleton_derivative {A : Set Ordinal.{u}} {η β : Ordinal.{u}}
    (e : OrdinalInterval β ≃ₜ A) (hsub : (ordinalDerived A η).Subsingleton) :
    (ordinalDerived (Iic β) η).Subsingleton := by
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
  have heq := ordinalDerived_image_closedEmbedding hf univ η
  rw [image_univ, hfrange] at heq
  have hdom : (ordinalDerived (univ : Set (OrdinalInterval β)) η).Subsingleton := by
    intro x hx y hy
    apply hf.injective
    apply hsub
    · rw [heq]
      exact mem_image_of_mem f hx
    · rw [heq]
      exact mem_image_of_mem f hy
  have hi := ordinalDerived_image_closedEmbedding
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{u}) β)).isClosedEmbedding_subtypeVal univ η
  rw [image_univ, Subtype.range_coe] at hi
  have hIcc : Icc (0 : Ordinal.{u}) β = Iic β := by ext x; simp
  have hi' : ordinalDerived (Iic β) η =
      (Subtype.val : OrdinalInterval β → Ordinal.{u}) ''
        ordinalDerived (univ : Set (OrdinalInterval β)) η := by
    calc
      ordinalDerived (Iic β) η = ordinalDerived (Icc (0 : Ordinal.{u}) β) η :=
        congrArg (fun S => ordinalDerived S η) hIcc.symm
      _ = _ := hi
  rw [hi']
  exact hdom.image _

/-- A compact ordinal set with a singleton positive-rank derivative is
homeomorphic to the corresponding pure ordinal power. -/
theorem ordinal_compact_singleton_derivative_homeomorph {A : Set Ordinal.{u}}
    (hA : IsCompact A) {η a : Ordinal.{u}} (hη : η ≠ 0)
    (hD : ordinalDerived A η = {a}) :
    Nonempty (OrdinalInterval (Ordinal.omega0 ^ η) ≃ₜ A) := by
  have hneD : (ordinalDerived A η).Nonempty := by rw [hD]; exact singleton_nonempty _
  have hneA : A.Nonempty := hneD.mono (by
    simpa using ordinalDerived_antitone hA.isClosed (show 0 ≤ η from bot_le))
  obtain ⟨β, e, _, _⟩ := ordinal_compact_order_homeomorph hA hneA
  have hle : Ordinal.omega0 ^ η ≤ β := ordinal_power_le_compact_model e hη hneD
  have hsub : (ordinalDerived (Iic β) η).Subsingleton :=
    ordinal_model_subsingleton_derivative e (by rw [hD]; exact subsingleton_singleton)
  have hne : (ordinalDerived (Iic β) η).Nonempty := by
    refine ⟨Ordinal.omega0 ^ η, ?_⟩
    rw [ordinalDerived_Iic, ordinalDerived_univ, if_neg hη]
    exact ⟨⟨Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero, dvd_refl _⟩, hle⟩
  have hlt := (ordinal_singleton_derivative_bounds hη hne hsub).2
  have htail : β - Ordinal.omega0 ^ η < Ordinal.omega0 ^ η :=
    (Ordinal.sub_lt_of_le hle).mpr hlt
  let eβ := (ordinalIntervalCongr (Ordinal.add_sub_cancel_of_le hle).symm).trans
    (ordinalPowerTailAbsorb hη htail)
  exact ⟨eβ.symm.trans e⟩

end ThesisCommon
