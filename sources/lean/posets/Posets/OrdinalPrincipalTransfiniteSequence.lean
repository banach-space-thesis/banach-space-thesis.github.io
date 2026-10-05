import Posets.OrdinalPrincipalCofinalSequence

/-! Genuine ordinal blocks indexed by a possibly uncountable cofinal ordinal.
The gap hypothesis bounds every preceding endpoint strictly below the next
one; it is an ordinal geometric condition, independent of all operators. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets
set_option maxHeartbeats 1000000

structure OrdinalPrincipalTransfiniteSequence (Λ Γ : Ordinal.{u}) where
  infinite : Ordinal.omega0 ≤ Λ
  endpoint : Iio Λ → Ordinal.{u}
  strictMono : StrictMono endpoint
  principal : ∀ i, Ordinal.Principal (· + ·) (endpoint i)
  head_large : Λ < endpoint ⟨0, Ordinal.omega0_pos.trans_le infinite⟩
  bound : ∀ i, endpoint i < Γ
  cofinal : ∀ β < Γ, ∃ i, β < endpoint i
  gap : ∀ i, ∃ b < endpoint i, ∀ j : Iio Λ, j < i → endpoint j < b

namespace OrdinalPrincipalTransfiniteSequence
variable {Λ Γ : Ordinal.{u}} (P : OrdinalPrincipalTransfiniteSequence Λ Γ)

def zeroIndex : Iio Λ := ⟨0, Ordinal.omega0_pos.trans_le P.infinite⟩

def predecessor (ξ : Ordinal.{u}) : Ordinal.{u} :=
  if hξ : ξ < Λ then P.endpoint ⟨ξ, hξ⟩ else Γ + ξ

@[simp] theorem predecessor_apply (i : Iio Λ) :
    P.predecessor i.val = P.endpoint i := by
  unfold predecessor
  split_ifs with hi
  · rfl
  · exact (hi i.property).elim

theorem predecessor_strictMono : StrictMono P.predecessor := by
  intro ξ η hξη
  by_cases hη : η < Λ
  · have hξ := hξη.trans hη
    simp only [predecessor, dif_pos hξ, dif_pos hη]
    exact P.strictMono hξη
  · by_cases hξ : ξ < Λ
    · simp only [predecessor, dif_pos hξ, dif_neg hη]
      exact (P.bound _).trans_le (Ordinal.le_add_right _ _)
    · simp only [predecessor, dif_neg hξ, dif_neg hη]
      exact (Ordinal.isNormal_add_right Γ).strictMono hξη

def boundary : Ordinal.{u} → Ordinal.{u} := JLMS.ordinalInitialSup P.predecessor

theorem boundary_isNormal : Ordinal.IsNormal P.boundary :=
  JLMS.ordinalInitialSup_isNormal _ P.predecessor_strictMono

@[simp] theorem boundary_zero : P.boundary 0 = 0 := JLMS.ordinalInitialSup_zero _

theorem boundary_succ (i : Iio Λ) :
    P.boundary (succ i.val) = succ (P.endpoint i) := by
  rw [boundary, JLMS.ordinalInitialSup_succ _ P.predecessor_strictMono.monotone,
    P.predecessor_apply]

theorem boundary_endpoint : P.boundary Λ = Γ := by
  apply le_antisymm
  · apply Ordinal.blsub_le
    intro ξ hξ
    simp only [predecessor, dif_pos hξ]
    exact P.bound _
  · by_contra hn
    obtain ⟨i, hi⟩ := P.cofinal _ (lt_of_not_ge hn)
    have hh := Ordinal.lt_blsub (fun ξ _ => P.predecessor ξ) i.val i.property
    rw [P.predecessor_apply] at hh
    exact hi.not_ge hh.le

theorem boundary_lt (i : Iio Λ) : P.boundary i.val < P.endpoint i := by
  obtain ⟨b, hb, hbelow⟩ := P.gap i
  apply lt_of_le_of_lt _ hb
  apply Ordinal.blsub_le
  intro ξ hξ
  have hξΛ := hξ.trans i.property
  simp only [predecessor, dif_pos hξΛ]
  exact hbelow ⟨ξ, hξΛ⟩ hξ

def blockMap : C(JLMS.OrdinalInterval Λ, JLMS.OrdinalInterval Γ) where
  toFun ξ := ⟨P.boundary ξ.val, Ordinal.zero_le _, by
    simpa only [P.boundary_endpoint] using P.boundary_isNormal.monotone ξ.property.2⟩
  continuous_toFun := (P.boundary_isNormal.continuous.comp continuous_subtype_val).subtype_mk _

theorem blockMap_strictMono : StrictMono P.blockMap :=
  fun _ _ h => P.boundary_isNormal.strictMono h

@[simp] theorem blockMap_zero : P.blockMap ⟨0, le_rfl, Ordinal.zero_le _⟩ =
    ⟨0, Ordinal.zero_le _, Ordinal.zero_le _⟩ := Subtype.ext P.boundary_zero

@[simp] theorem blockMap_endpoint : P.blockMap ⟨Λ, Ordinal.zero_le _, le_rfl⟩ =
    ⟨Γ, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext P.boundary_endpoint

theorem blockMap_length (i : Iio Λ) :
    JLMS.ordinalSpaceBlockLength P.blockMap i = succ (P.endpoint i) := by
  have ha : P.boundary i.val + succ (P.endpoint i) = succ (P.endpoint i) := by
    rw [Ordinal.add_succ]
    exact congrArg succ (Ordinal.principal_add_iff_add_left_eq_self.mp (P.principal i) _
      (P.boundary_lt i))
  change P.boundary (succ i.val) - P.boundary i.val = _
  rw [P.boundary_succ]
  calc
    _ = (P.boundary i.val + succ (P.endpoint i)) - P.boundary i.val := by rw [ha]
    _ = succ (P.endpoint i) := Ordinal.add_sub_cancel _ _

theorem blockMap_infinite_blocks (i : Iio Λ) :
    Ordinal.omega0 ≤ JLMS.ordinalSpaceBlockLength P.blockMap i := by
  rw [P.blockMap_length]
  exact ((P.infinite.trans P.head_large.le).trans
    (P.strictMono.monotone (Ordinal.zero_le i.val))).trans (Order.le_succ _)

end OrdinalPrincipalTransfiniteSequence
end Posets
