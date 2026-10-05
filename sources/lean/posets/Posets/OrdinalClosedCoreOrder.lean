import Posets.OrdinalClosedCoreBands
import Posets.OrdinalClosedCopyCeilingImageRank

/-! The actual increasing ordinal model of a closed colour core.
Cantor--Bendixson rank gives a lower bound for its ordinal endpoint and
order type, with no countability or metrizability hypothesis. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon

theorem ordinalClosedCore_order_model {θ ρ : Ordinal.{u}}
    (C : Set (Iic θ)) (hC : IsCompact C) (hρ : ρ ≠ 0)
    (hrank : (ordinalDerived C ρ).Nonempty) :
    ∃ β : Ordinal.{u}, ∃ e : OrdinalInterval β ≃ₜ (Subtype.val '' C : Set Ordinal.{u}),
      StrictMono (fun x => (e x).val) ∧ Ordinal.omega0 ^ ρ ≤ β ∧ β ≤ θ := by
  have hne : C.Nonempty := by
    have h := hrank.mono (ordinalDerived_antitone hC.isClosed (Ordinal.zero_le ρ))
    simpa only [ordinalDerived_zero] using h
  have hA : IsCompact (Subtype.val '' C : Set Ordinal.{u}) := hC.image continuous_subtype_val
  have hArank : (ordinalDerived (Subtype.val '' C : Set Ordinal.{u}) ρ).Nonempty := by
    rw [ordinalDerived_image_closedEmbedding isClosed_Iic.isClosedEmbedding_subtypeVal]
    exact hrank.image Subtype.val
  obtain ⟨β, e, he, hβ⟩ := ordinal_compact_order_homeomorph hA (hne.image Subtype.val)
  refine ⟨β, e, he, ordinal_power_le_compact_model e hρ hArank, hβ.trans ?_⟩
  apply csSup_le (hne.image Subtype.val)
  rintro y ⟨x, _, rfl⟩
  exact x.property

theorem ordinalClosedCore_order_type_lower {θ ρ : Ordinal.{u}}
    (C : Set (Iic θ)) (hC : IsCompact C) (hρ : ρ ≠ 0)
    (hrank : (ordinalDerived C ρ).Nonempty) :
    Ordinal.lift.{u+1} (Order.succ (Ordinal.omega0 ^ ρ)) ≤
      Ordinal.type (· < · : (Subtype.val '' C : Set Ordinal.{u}) → _ → Prop) := by
  obtain ⟨β, e, he, hβ, _⟩ := ordinalClosedCore_order_model C hC hρ hrank
  rw [ordinal_type_compact_order_model e he]
  exact Ordinal.lift_le.mpr (Order.succ_le_succ hβ)

/-- A closed core retaining the top rank in the corresponding power interval
has its full original ordinal type, including the final point. -/
theorem ordinalClosedCore_full_power_model {ρ : Ordinal.{u}} (hρ : ρ ≠ 0)
    (C : Set (Iic (Ordinal.omega0 ^ ρ))) (hC : IsCompact C)
    (hrank : (ordinalDerived C ρ).Nonempty) :
    ∃ e : OrdinalInterval (Ordinal.omega0 ^ ρ) ≃ₜ
        (Subtype.val '' C : Set Ordinal.{u}), StrictMono (fun x => (e x).val) := by
  obtain ⟨β, e, he, hlo, hhi⟩ := ordinalClosedCore_order_model C hC hρ hrank
  have hβ : β = Ordinal.omega0 ^ ρ := le_antisymm hhi hlo
  subst β
  exact ⟨e, he⟩

theorem ordinalClosedCore_full_power_type {ρ : Ordinal.{u}} (hρ : ρ ≠ 0)
    (C : Set (Iic (Ordinal.omega0 ^ ρ))) (hC : IsCompact C)
    (hrank : (ordinalDerived C ρ).Nonempty) :
    Ordinal.type (· < · : (Subtype.val '' C : Set Ordinal.{u}) → _ → Prop) =
      Ordinal.lift.{u+1} (Order.succ (Ordinal.omega0 ^ ρ)) := by
  obtain ⟨e, he⟩ := ordinalClosedCore_full_power_model hρ C hC hrank
  exact ordinal_type_compact_order_model e he

/-- Conversely, large order type in an actual compact ordinal subset gives
the corresponding nonempty derivative. -/
theorem ordinalClosedCore_rank_of_order_type {F : Set Ordinal.{u}} {ρ : Ordinal.{u}}
    (hF : IsCompact F) (hρ : ρ ≠ 0)
    (htype : Ordinal.lift.{u+1} (Order.succ (Ordinal.omega0 ^ ρ)) ≤
      Ordinal.type (· < · : F → _ → Prop)) :
    (ordinalDerived F ρ).Nonempty := by
  have hne : F.Nonempty := by
    by_contra h
    letI : IsEmpty F := ⟨fun x => h ⟨x.val, x.property⟩⟩
    rw [Ordinal.type_eq_zero_of_empty] at htype
    have hz : 0 < Ordinal.lift.{u+1} (Order.succ (Ordinal.omega0 ^ ρ)) := by
      simpa only [Ordinal.lift_zero] using Ordinal.lift_lt.mpr (Ordinal.succ_pos (Ordinal.omega0 ^ ρ))
    exact hz.not_ge htype
  obtain ⟨β, e, he, _⟩ := ordinal_compact_order_homeomorph hF hne
  rw [ordinal_type_compact_order_model e he] at htype
  have hβ : Ordinal.omega0 ^ ρ ≤ β := Order.succ_le_succ_iff.mp (Ordinal.lift_le.mp htype)
  have hI : (ordinalDerived (Iic β) ρ).Nonempty := by
    apply Set.Nonempty.mono (ordinalDerived_mono (Iic_subset_Iic.mpr hβ) ρ)
    rw [ordinalDerived_Iic_power_self hρ]
    exact singleton_nonempty _
  have hIcc : (ordinalDerived (Icc (0 : Ordinal.{u}) β) ρ).Nonempty := by
    have heq : Icc (0 : Ordinal.{u}) β = Iic β := by ext x; simp
    rwa [heq]
  have hi := ordinalDerived_image_closedEmbedding
    (isClosed_Icc : IsClosed (Icc (0 : Ordinal.{u}) β)).isClosedEmbedding_subtypeVal univ ρ
  rw [image_univ, Subtype.range_coe] at hi
  rw [hi] at hIcc
  have hdom : (ordinalDerived (univ : Set (OrdinalInterval β)) ρ).Nonempty :=
    image_nonempty.mp hIcc
  let f : OrdinalInterval β → Ordinal.{u} := fun x => (e x).val
  have hf : IsClosedEmbedding f := (continuous_subtype_val.comp e.continuous).isClosedEmbedding
    (Subtype.val_injective.comp e.injective)
  have hfrange : range f = F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  have heq := ordinalDerived_image_closedEmbedding hf univ ρ
  rw [image_univ, hfrange] at heq
  rw [heq]
  exact hdom.image f

variable {𝕜 : Type*} [RCLike 𝕜] {θ γ : Ordinal.{u}}

theorem ordinalClosedCore_coloured_band_order_model (hθ : θ ∈ ordinalTowerLevel θ γ)
    (M : JLMS.AtomicDualModel 𝕜 (Iic θ))
    (T S : JLMS.CZero 𝕜 (Iic θ) →L[𝕜] JLMS.CZero 𝕜 (Iic θ))
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (a : ℕ → Iic γ) (ha : Monotone a) {N : ℕ} {ε : ℝ}
    (hN : ‖T‖ + ‖S‖ < N * ε) (ρ : Ordinal.{u}) (hρ : ρ ≠ 0) {x : Iic θ}
    (hx : x ∈ ordinalDerived (univ : Set (Iic θ)) ρ) :
    ∃ i : Fin N × Bool, ∃ β : Ordinal.{u},
      ∃ e : OrdinalInterval β ≃ₜ
        (Subtype.val '' closure (ordinalClosedCoreBandLeaves hθ M T S a i.1.val i.2 ε) : Set Ordinal.{u}),
      StrictMono (fun y => (e y).val) ∧ Ordinal.omega0 ^ ρ ≤ β ∧ β ≤ θ := by
  obtain ⟨i, hi⟩ := ordinalClosedCore_exists_coloured_band hθ M T S hTS a ha hN ρ hx
  obtain ⟨β, e, he, hlo, hhi⟩ := ordinalClosedCore_order_model _
    (ordinalClosedCoreBandLeaves_isCompact hθ M T S a i.1.val i.2 ε) hρ ⟨x, hi⟩
  exact ⟨i, β, e, he, hlo, hhi⟩

end Posets
