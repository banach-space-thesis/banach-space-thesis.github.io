/- Universe-polymorphic extension of Posets.OrdinalFixedExponentMiddle; real and complex scalar fields remain in Type zero. -/
import Posets.OrdinalRegularOmegaMiddle

/-! Actual qualitative normalization around a fixed initial-base exponent.
For any infinite initial κ and g ≥ 2 with card g ≤ κ, the spaces C[0,α]
with κ^g ≤ α < κ^(g·ω) are isomorphic to C[0,κ^g]. No regularity or
principality of g is required. The last theorem reduces every α ≥ κ²
with card α ≤ κ to g = 2 or an infinite additive principal exponent.
The equivalences may have bounds depending on the exponent; the explicit
factorisation transports require the property of the canonical space. -/

noncomputable section
universe u
namespace LPCK.GenericOrdinal
open JLMS ThesisCommon Posets
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000

local instance fixedMiddleEndpointGroup (α : Ordinal.{u}) :
    NormedAddCommGroup (ordinalEndpointZero 𝕜 α) := inferInstance
local instance fixedMiddleEndpointSpace (α : Ordinal.{u}) :
    NormedSpace 𝕜 (ordinalEndpointZero 𝕜 α) := inferInstance
local instance fixedMiddleSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (CZeroSum 𝕜 E) := inferInstance
local instance fixedMiddleSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (CZeroSum 𝕜 E) := inferInstance

abbrev OrdinalFixedExponentEndpoint (𝕜 : Type) [RCLike 𝕜]
    (c : Cardinal.{u}) (g : Ordinal.{u}) := ↥(ordinalEndpointZero 𝕜 (c.ord ^ g))

theorem ordinalFixedExponent_base_card (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hgcard : g.card ≤ c) :
    (c.ord ^ g).card ≤ c := by
  have h := Ordinal.card_opow_le_of_omega0_le_left (Cardinal.omega0_le_ord.mpr hc) g
  simpa only [Cardinal.card_ord, max_eq_left hgcard] using h

def ordinalFixedExponentEndpointReplication (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c) :
    OrdinalFixedExponentEndpoint 𝕜 c g ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio c.ord => OrdinalFixedExponentEndpoint 𝕜 c g) :=
  Classical.choice (nonempty_ordinalEndpointZeroPowerReplication c hc g hg hgcard)

def ordinalFixedExponentEndpointSmallerReplication (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (η : Ordinal.{u}) (hη : Ordinal.omega0 ≤ η) (hηcard : η.card ≤ c) :
    OrdinalFixedExponentEndpoint 𝕜 c g ≃L[𝕜]
      CZeroSum 𝕜 (fun _ : Set.Iio η => OrdinalFixedExponentEndpoint 𝕜 c g) := by
  letI : Infinite (Set.Iio c.ord) := ordinalIioInfinite _ (Cardinal.omega0_le_ord.mpr hc)
  letI : Infinite (Set.Iio η) := ordinalIioInfinite _ hη
  apply cZeroSum_smallerReplication _ (ordinalFixedExponentEndpointReplication c hc g hg hgcard)
  simpa only [Ordinal.mk_Iio_ordinal, Cardinal.card_ord] using Cardinal.lift_le.mpr hηcard

def ordinalFixedExponentConstantSumEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (η : Ordinal.{u}) (hη : Ordinal.omega0 ≤ η) (hηcard : η.card ≤ c)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : X ≃L[𝕜] OrdinalFixedExponentEndpoint 𝕜 c g) :
    CZeroSum 𝕜 (fun _ : Set.Iio η => X) ≃L[𝕜] OrdinalFixedExponentEndpoint 𝕜 c g :=
  (CZeroSum.congrRight (fun _ => e) (norm_nonneg _) (norm_nonneg _)
    (fun _ => le_rfl) (fun _ => le_rfl)).trans
      (ordinalFixedExponentEndpointSmallerReplication c hc g hg hgcard η hη hηcard).symm

def ordinalFixedExponentEndpointMultiplyEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (α η : Ordinal.{u}) (hα : Ordinal.omega0 ≤ α) (hη : Ordinal.omega0 ≤ η)
    (hηcard : η.card ≤ c) (habs : η = α ∨ η + α = α)
    (e : ordinalEndpointZero 𝕜 α ≃L[𝕜] OrdinalFixedExponentEndpoint 𝕜 c g) :
    ordinalEndpointZero 𝕜 (α * η) ≃L[𝕜] OrdinalFixedExponentEndpoint 𝕜 c g :=
  (ordinalEndpointZeroMultipleSumEquiv α η hα hη habs).trans
    (ordinalFixedExponentConstantSumEquiv c hc g hg hgcard η hη hηcard e)

def ordinalFixedExponentEndpointMultipleEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (n : ℕ) :
    ordinalEndpointZero 𝕜 (c.ord ^ (g * ((n+1 : ℕ) : Ordinal.{u}))) ≃L[𝕜]
      OrdinalFixedExponentEndpoint 𝕜 c g := by
  induction n with
  | zero =>
      rw [show ((0+1 : ℕ) : Ordinal.{u}) = 1 by norm_num, mul_one]
  | succ n ih =>
      have hκ : 0 < c.ord := Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)
      have hlo : c.ord ^ g ≤ c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) :=
        Ordinal.opow_le_opow_right hκ (Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n))
      have hinf := ordinalInitialPower_infinite c hc g (one_le_two.trans hg)
      have habs : c.ord ^ g = c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) ∨
          c.ord ^ g + c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) =
            c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) := by
        rcases hlo.eq_or_lt with h | h
        · exact Or.inl h
        · exact Or.inr (Ordinal.principal_add_iff_add_left_eq_self.mp
            (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _) _ h)
      have he : c.ord ^ (g * ((n+1+1 : ℕ) : Ordinal.{u})) =
          c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) * c.ord ^ g := by
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Ordinal.opow_add]
      exact (ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
        (ordinalFixedExponentEndpointMultiplyEquiv c hc g hg hgcard _ _
          (hinf.trans hlo) hinf (ordinalFixedExponent_base_card c hc g hgcard) habs ih)

/-- The residual exponent is absorbed by a single ordinal multiplication,
using the actual replication of the fixed canonical space. -/
def ordinalFixedExponentEndpointRemainderEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (n : ℕ) (δ : Ordinal.{u}) (hδ : δ < g) :
    ordinalEndpointZero 𝕜 (c.ord ^ (g * ((n+1 : ℕ) : Ordinal.{u}) + δ)) ≃L[𝕜]
      OrdinalFixedExponentEndpoint 𝕜 c g := by
  by_cases hδ0 : δ = 0
  · subst δ
    rw [add_zero]
    exact ordinalFixedExponentEndpointMultipleEquiv c hc g hg hgcard n
  have hδ1 : 1 ≤ δ := Ordinal.one_le_iff_ne_zero.mpr hδ0
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hδg : c.ord ^ δ < c.ord ^ g := (Ordinal.opow_lt_opow_iff_right hκ).mpr hδ
  have hggn : g ≤ g * ((n+1 : ℕ) : Ordinal) :=
    Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos n)
  have hδcard : δ.card ≤ c := (Ordinal.card_le_card hδ.le).trans hgcard
  have habs : c.ord ^ δ + c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) =
      c.ord ^ (g * ((n+1 : ℕ) : Ordinal)) :=
    Ordinal.principal_add_iff_add_left_eq_self.mp
      (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) _) _
        (hδg.trans_le (Ordinal.opow_le_opow_right (zero_lt_one.trans hκ) hggn))
  rw [Ordinal.opow_add]
  exact ordinalFixedExponentEndpointMultiplyEquiv c hc g hg hgcard _ _
    (ordinalInitialPower_infinite c hc _ (one_le_two.trans (hg.trans hggn)))
    (ordinalInitialPower_infinite c hc δ hδ1)
    (ordinalFixedExponent_base_card c hc δ hδcard) (Or.inr habs)
    (ordinalFixedExponentEndpointMultipleEquiv c hc g hg hgcard n)

def ordinalFixedExponentEndpointPowerEquiv (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (β : Ordinal.{u}) (hlo : g ≤ β) (hhi : β < g * Ordinal.omega0) :
    ordinalEndpointZero 𝕜 (c.ord ^ β) ≃L[𝕜] OrdinalFixedExponentEndpoint 𝕜 c g := by
  refine Classical.choice ?_
  have hg0 : g ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : Ordinal.{u}) < 2) hg).ne'
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ((Ordinal.div_lt hg0).mpr hhi)
  have hnpos : 0 < n := by
    have hp : 0 < β / g := (Ordinal.div_pos hg0).mpr hlo
    have : (0 : Ordinal.{u}) < (n : Ordinal) := by simpa only [← hn] using hp
    exact_mod_cast this
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have he : β = g * ((m+1 : ℕ) : Ordinal) + β % g := by
    rw [← hn]
    exact (Ordinal.div_add_mod β g).symm
  exact ⟨(ordinalEndpointZeroCongrIsometry (𝕜 := 𝕜)
    (congrArg (fun x => c.ord ^ x) he)).toContinuousLinearEquiv.trans
      (ordinalFixedExponentEndpointRemainderEquiv c hc g hg hgcard m _ (Ordinal.mod_lt β hg0))⟩

def ordinalFixedExponentPowerEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (β : Ordinal.{u}) (hlo : g ≤ β) (hhi : β < g * Ordinal.omega0) :
    JLMS.OrdinalC 𝕜 (c.ord ^ β) ≃L[𝕜] JLMS.OrdinalC 𝕜 (c.ord ^ g) :=
  (ordinalSpaceEndpointZeroBoundedEquiv _
    (ordinalInitialPower_infinite c hc β (one_le_two.trans (hg.trans hlo)))).trans
      ((ordinalFixedExponentEndpointPowerEquiv c hc g hg hgcard β hlo hhi).trans
        (ordinalSpaceEndpointZeroBoundedEquiv _
          (ordinalInitialPower_infinite c hc g (one_le_two.trans hg))).symm)

def ordinalFixedExponentPowerMultipleEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (β : Ordinal.{u}) (hlo : g ≤ β) (hhi : β < g * Ordinal.omega0)
    (η : Ordinal.{u}) (hη : 0 < η) (hηκ : η < c.ord) :
    JLMS.OrdinalC 𝕜 (c.ord ^ β * η) ≃L[𝕜] JLMS.OrdinalC 𝕜 (c.ord ^ g) := by
  refine Classical.choice ?_
  have hβ : 1 ≤ β := one_le_two.trans (hg.trans hlo)
  have hinf := ordinalInitialPower_infinite c hc β hβ
  by_cases hηω : η < Ordinal.omega0
  · obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hηω
    have hmpos : 0 < m := by
      have : (0 : Ordinal.{u}) < (m : Ordinal) := by simpa only [← hm] using hη
      exact_mod_cast this
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hm]
    exact ⟨(ordinalSpaceFinitePower (𝕜 := 𝕜) _ hinf n).trans
      ((ContinuousLinearEquiv.piCongrRight
        (fun _ : Fin (n+1) => ordinalFixedExponentPowerEquiv c hc g hg hgcard β hlo hhi)).trans
          (finitePiCollapseEquiv (ordinalSpaceInitialPowerSquareEquiv c hc g hg hgcard) n))⟩
  · have hκ : c.ord ≤ c.ord ^ β := by
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right
        (Ordinal.omega0_pos.trans_le (Cardinal.omega0_le_ord.mpr hc)) hβ
    have habs : η + c.ord ^ β = c.ord ^ β :=
      Ordinal.principal_add_iff_add_left_eq_self.mp
        (Ordinal.principal_add_opow_of_principal_add (Ordinal.principal_add_ord hc) β)
        η (hηκ.trans_le hκ)
    exact ⟨(ordinalSpaceEndpointZeroBoundedEquiv (𝕜 := 𝕜) _
      (hinf.trans (Ordinal.le_mul_left _ hη))).trans
        ((ordinalFixedExponentEndpointMultiplyEquiv c hc g hg hgcard _ η hinf
          (le_of_not_gt hηω) (Cardinal.lt_ord.mp hηκ).le (Or.inr habs)
          (ordinalFixedExponentEndpointPowerEquiv c hc g hg hgcard β hlo hhi)).trans
            (ordinalSpaceEndpointZeroBoundedEquiv _
              (ordinalInitialPower_infinite c hc g (one_le_two.trans hg))).symm)⟩

/-- The fixed-exponent middle interval, for every infinite initial base. -/
def ordinalFixedExponentMiddleEquiv (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (α : Ordinal.{u}) (hlo : c.ord ^ g ≤ α) (hhi : α < c.ord ^ (g * Ordinal.omega0)) :
    JLMS.OrdinalC 𝕜 α ≃L[𝕜] JLMS.OrdinalC 𝕜 (c.ord ^ g) := by
  refine Classical.choice ?_
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hα : α ≠ 0 := ((Ordinal.opow_pos _ (zero_lt_one.trans hκ)).trans_le hlo).ne'
  let β := Ordinal.log c.ord α
  have hβ : g ≤ β := Ordinal.le_log_of_opow_le hκ hlo
  have hβhi : β < g * Ordinal.omega0 := (Ordinal.lt_opow_iff_log_lt hκ hα).mp hhi
  let η := α / (c.ord ^ β)
  have hη : 0 < η := Ordinal.div_opow_log_pos c.ord hα
  have hηκ : η < c.ord := Ordinal.div_opow_log_lt α hκ
  let ρ := α % (c.ord ^ β)
  have hρ : ρ < c.ord ^ β := Ordinal.mod_lt _ (Ordinal.opow_pos β (zero_lt_one.trans hκ)).ne'
  have he : α = c.ord ^ β * η + ρ := (Ordinal.div_add_mod α _).symm
  exact ⟨(ordinalSpaceCongrIsometry (𝕜 := 𝕜) he).toContinuousLinearEquiv.trans
    ((ordinalSpacePowerRemainder c hc β η ρ (one_le_two.trans (hg.trans hβ)) hη hρ).trans
      (ordinalFixedExponentPowerMultipleEquiv c hc g hg hgcard β hβ hβhi η hη hηκ))⟩

theorem ordinalFixedExponentMiddle_hasUPFP_of_base (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (g : Ordinal.{u}) (hg : 2 ≤ g) (hgcard : g.card ≤ c)
    (hbase : HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 (c.ord ^ g)))
    (α : Ordinal.{u}) (hlo : c.ord ^ g ≤ α) (hhi : α < c.ord ^ (g * Ordinal.omega0)) :
    HasUPFP 𝕜 (JLMS.OrdinalC 𝕜 α) :=
  hbase.of_equiv (ordinalFixedExponentMiddleEquiv c hc g hg hgcard α hlo hhi).symm

/-- Every exponent at least two lies in the middle interval of a canonical
exponent, either two or an infinite additive principal ordinal. -/
theorem exists_ordinalFixedExponentCanonical (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (β : Ordinal.{u}) (hβ : 2 ≤ β) (hβcard : β.card ≤ c) :
    ∃ g : Ordinal.{u}, 2 ≤ g ∧ g.card ≤ c ∧
      (g = 2 ∨ (Ordinal.omega0 ≤ g ∧ Ordinal.Principal (· + ·) g)) ∧
      g ≤ β ∧ β < g * Ordinal.omega0 := by
  by_cases hβω : β < Ordinal.omega0
  · refine ⟨2, le_rfl, ?_, Or.inl rfl, hβ, ?_⟩
    · exact (Ordinal.card_le_card (Ordinal.nat_lt_omega0 2).le).trans
        (by simpa only [Ordinal.card_omega0] using hc)
    · exact hβω.trans_le (Ordinal.le_mul_right _ (by norm_num : (0 : Ordinal.{u}) < 2))
  · let g := Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 β
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : Ordinal.{u}) < 2) hβ).ne'
    have hgβ : g ≤ β := Ordinal.opow_log_le_self _ hβ0
    have hgω : Ordinal.omega0 ≤ g := by
      have ht : (1 : Ordinal.{u}) ≤ Ordinal.log Ordinal.omega0 β :=
        Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 (by
          simpa only [Ordinal.opow_one] using le_of_not_gt hβω)
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos ht
    refine ⟨g, (Ordinal.nat_lt_omega0 2).le.trans hgω,
      (Ordinal.card_le_card hgβ).trans hβcard,
      Or.inr ⟨hgω, Ordinal.principal_add_omega0_opow _⟩, hgβ, ?_⟩
    simpa only [g, Ordinal.opow_succ] using
      Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 β

/-- A genuine Banach-space equivalence to a canonical initial-base power;
no factorisation property is assumed in this normalization. -/
theorem exists_ordinalSpace_canonical_power_normalForm (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (α : Ordinal.{u}) (hcard : α.card ≤ c)
    (hα : c.ord ^ (2 : Ordinal) ≤ α) :
    ∃ g : Ordinal.{u}, 2 ≤ g ∧ g.card ≤ c ∧
      (g = 2 ∨ (Ordinal.omega0 ≤ g ∧ Ordinal.Principal (· + ·) g)) ∧
      Nonempty (JLMS.OrdinalC 𝕜 α ≃L[𝕜] JLMS.OrdinalC 𝕜 (c.ord ^ g)) := by
  have hκ : 1 < c.ord := Ordinal.one_lt_omega0.trans_le (Cardinal.omega0_le_ord.mpr hc)
  have hα0 : α ≠ 0 := ((Ordinal.opow_pos _ (zero_lt_one.trans hκ)).trans_le hα).ne'
  let β := Ordinal.log c.ord α
  have hβ : 2 ≤ β := Ordinal.le_log_of_opow_le hκ hα
  have hβcard : β.card ≤ c := (Ordinal.card_le_card (Ordinal.log_le_self _ _)).trans hcard
  obtain ⟨g, hg, hgcard, hgc, hgb, hbg⟩ := exists_ordinalFixedExponentCanonical c hc β hβ hβcard
  refine ⟨g, hg, hgcard, hgc, ⟨ordinalFixedExponentMiddleEquiv c hc g hg hgcard α ?_ ?_⟩⟩
  · exact (Ordinal.opow_le_opow_right (zero_lt_one.trans hκ) hgb).trans
      (Ordinal.opow_log_le_self c.ord hα0)
  · exact (Ordinal.lt_opow_iff_log_lt hκ hα0).mpr hbg

end LPCK.GenericOrdinal
