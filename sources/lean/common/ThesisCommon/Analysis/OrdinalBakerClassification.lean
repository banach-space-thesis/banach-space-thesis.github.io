import ThesisCommon.Analysis.OrdinalFiniteAbsorption
import ThesisCommon.Analysis.OrdinalBakerSingleton

/-! Normalization of every infinite compact ordinal set to [0,ω^η n],
where η is positive and n is a positive natural number. Both the rank
existence and the homeomorphism are proved; no classification is assumed. -/

noncomputable section
open Set Order Topology
universe u
namespace ThesisCommon

theorem ordinal_finite_derivative_quotient_lt_omega {η β : Ordinal.{u}} (hη : η ≠ 0)
    (hfin : (ordinalDerived (Iic β) η).Finite) :
    β / (Ordinal.omega0 ^ η) < Ordinal.omega0 := by
  classical
  by_contra h
  have hq : Ordinal.omega0 ≤ β / (Ordinal.omega0 ^ η) := le_of_not_gt h
  have hp : 0 < Ordinal.omega0 ^ η := Ordinal.opow_pos η Ordinal.omega0_pos
  let f : ℕ → Ordinal.{u} := fun n => Ordinal.omega0 ^ η * ((n + 1 : ℕ) : Ordinal)
  have hinj : Function.Injective f := by
    intro n m hnm
    have hnm' : ((n + 1 : ℕ) : Ordinal.{u}) = ((m + 1 : ℕ) : Ordinal.{u}) :=
      (Ordinal.isNormal_mul_right hp).strictMono.injective hnm
    exact Nat.succ_injective (Nat.cast_injective hnm')
  have hsub : range f ⊆ ordinalDerived (Iic β) η := by
    rintro _ ⟨n, rfl⟩
    rw [ordinalDerived_Iic, ordinalDerived_univ, if_neg hη]
    have hn : ((n + 1 : ℕ) : Ordinal.{u}) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    refine ⟨⟨mul_ne_zero hp.ne' hn, dvd_mul_right _ _⟩, ?_⟩
    exact (mul_le_mul_left' ((Ordinal.nat_lt_omega0 (n + 1)).le.trans hq)
      (Ordinal.omega0 ^ η)).trans (Ordinal.mul_div_le β (Ordinal.omega0 ^ η))
  exact (Set.infinite_range_of_injective hinj) (hfin.subset hsub)

theorem ordinal_model_finite_derivative {A : Set Ordinal.{u}} {η β : Ordinal.{u}}
    (e : OrdinalInterval β ≃ₜ A) (hfin : (ordinalDerived A η).Finite) :
    (ordinalDerived (Iic β) η).Finite := by
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
  rw [heq] at hfin
  have hdom : (ordinalDerived (univ : Set (OrdinalInterval β)) η).Finite :=
    hfin.of_finite_image hf.injective.injOn
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

/-- The general infinite compact ordinal normalization required by the
paper's reduction to finite multiples of powers of omega. -/
theorem ordinal_compact_infinite_normal_form {A : Set Ordinal.{u}}
    (hA : IsCompact A) (hInf : A.Infinite) :
    ∃ η : Ordinal.{u}, ∃ n : ℕ, η ≠ 0 ∧ 0 < n ∧
      Nonempty (A ≃ₜ OrdinalInterval (Ordinal.omega0 ^ η * (n : Ordinal))) := by
  obtain ⟨η, hfin, hne, _⟩ := ordinal_exists_finite_nonempty_derivative hA hInf.nonempty
  have hη : η ≠ 0 := by
    intro hz
    subst η
    exact hInf (by simpa only [ordinalDerived_zero] using hfin)
  obtain ⟨β, e, _, _⟩ := ordinal_compact_order_homeomorph hA hInf.nonempty
  have hp := Ordinal.opow_pos η Ordinal.omega0_pos
  have hle := ordinal_power_le_compact_model e hη hne
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp
    (ordinal_finite_derivative_quotient_lt_omega hη (ordinal_model_finite_derivative e hfin))
  have hnpos : 0 < n := by
    have hq := (Ordinal.div_pos hp.ne').mpr hle
    rw [hn] at hq
    exact_mod_cast hq
  have hmod : β % (Ordinal.omega0 ^ η) < Ordinal.omega0 ^ η := Ordinal.mod_lt _ hp.ne'
  have hβ : Ordinal.omega0 ^ η * (n : Ordinal) + β % (Ordinal.omega0 ^ η) = β := by
    simpa only [hn] using Ordinal.div_add_mod β (Ordinal.omega0 ^ η)
  let eβ := (ordinalIntervalCongr hβ.symm).trans (ordinalPowerNatTailAbsorb hη hmod n hnpos)
  exact ⟨η, n, hη, hnpos, ⟨e.symm.trans eβ⟩⟩

end ThesisCommon
