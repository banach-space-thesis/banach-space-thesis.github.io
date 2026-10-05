import Posets.OrdinalRegularOmegaBlockModelGeometry

/-! A concrete cofinal sequence of principal ordinal blocks, allowing
the rank unit to vary from one block to the next. -/

noncomputable section
open Set Order Topology
universe u
namespace Posets

structure OrdinalPrincipalCofinalSequence (Γ : Ordinal.{u}) where
  endpoint : ℕ → Ordinal.{u}
  strictMono : StrictMono endpoint
  principal : ∀ i, Ordinal.Principal (· + ·) (endpoint i)
  limit : ∀ i, IsSuccLimit (endpoint i)
  head_large : Ordinal.omega0 < endpoint 0
  bound : ∀ i, endpoint i < Γ
  cofinal : ∀ β < Γ, ∃ i, β < endpoint i

namespace OrdinalPrincipalCofinalSequence
variable {Γ : Ordinal.{u}} (P : OrdinalPrincipalCofinalSequence Γ)

def predecessor (ξ : Ordinal.{u}) : Ordinal.{u} :=
  if hξ : ξ < Ordinal.omega0 then P.endpoint (ordinalOmegaFiniteIndex ξ hξ) else Γ + ξ

@[simp] theorem predecessor_nat (n : ℕ) : P.predecessor (n : Ordinal) = P.endpoint n := by
  simp [predecessor, Ordinal.nat_lt_omega0]

theorem predecessor_strictMono : StrictMono P.predecessor := by
  intro ξ η hξη
  by_cases hη : η < Ordinal.omega0
  · have hξ := hξη.trans hη
    obtain ⟨i, rfl⟩ := Ordinal.lt_omega0.mp hξ
    obtain ⟨j, rfl⟩ := Ordinal.lt_omega0.mp hη
    simp only [predecessor_nat]
    exact P.strictMono (by exact_mod_cast hξη)
  · by_cases hξ : ξ < Ordinal.omega0
    · simp only [predecessor, dif_pos hξ, dif_neg hη]
      exact (P.bound _).trans_le (Ordinal.le_add_right _ _)
    · simp only [predecessor, dif_neg hξ, dif_neg hη]
      exact (Ordinal.isNormal_add_right Γ).strictMono hξη

def boundary : Ordinal.{u} → Ordinal.{u} := JLMS.ordinalInitialSup P.predecessor

theorem boundary_isNormal : Ordinal.IsNormal P.boundary :=
  JLMS.ordinalInitialSup_isNormal _ P.predecessor_strictMono

@[simp] theorem boundary_zero : P.boundary 0 = 0 := JLMS.ordinalInitialSup_zero _

theorem boundary_succ (n : ℕ) : P.boundary ((n+1 : ℕ) : Ordinal) = succ (P.endpoint n) := by
  rw [Ordinal.natCast_succ, boundary,
    JLMS.ordinalInitialSup_succ _ P.predecessor_strictMono.monotone, predecessor_nat]

theorem boundary_omega : P.boundary Ordinal.omega0 = Γ := by
  apply le_antisymm
  · apply Ordinal.blsub_le
    intro ξ hξ
    simp only [predecessor, dif_pos hξ]
    exact P.bound _
  · by_contra hn
    obtain ⟨i, hi⟩ := P.cofinal _ (lt_of_not_ge hn)
    have hh := Ordinal.lt_blsub (fun ξ _ => P.predecessor ξ) (i : Ordinal)
      (Ordinal.nat_lt_omega0 i)
    simp only [predecessor_nat] at hh
    exact hi.not_ge hh.le

def blockMap : C(JLMS.OrdinalInterval (Ordinal.omega0 : Ordinal.{u}), JLMS.OrdinalInterval Γ) where
  toFun ξ := ⟨P.boundary ξ.val, Ordinal.zero_le _, by
    simpa only [P.boundary_omega] using P.boundary_isNormal.monotone ξ.property.2⟩
  continuous_toFun := (P.boundary_isNormal.continuous.comp continuous_subtype_val).subtype_mk _

theorem blockMap_strictMono : StrictMono P.blockMap := fun _ _ h => P.boundary_isNormal.strictMono h

@[simp] theorem blockMap_zero : P.blockMap ⟨0, le_rfl, Ordinal.zero_le _⟩ =
    ⟨0, Ordinal.zero_le _, Ordinal.zero_le _⟩ := Subtype.ext P.boundary_zero

@[simp] theorem blockMap_endpoint : P.blockMap ⟨Ordinal.omega0, Ordinal.zero_le _, le_rfl⟩ =
    ⟨Γ, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext P.boundary_omega

theorem boundary_nat_lt (n : ℕ) : P.boundary (n : Ordinal) < P.endpoint n := by
  cases n with
  | zero => simpa only [Nat.cast_zero, P.boundary_zero] using
      Ordinal.omega0_pos.trans P.head_large
  | succ n =>
      rw [P.boundary_succ]
      exact (P.limit _).succ_lt (P.strictMono (Nat.lt_succ_self n))

theorem blockMap_length (n : ℕ) :
    JLMS.ordinalSpaceBlockLength P.blockMap (ordinalOmegaNatIndexEquiv n) = succ (P.endpoint n) := by
  have ha : P.boundary (n : Ordinal) + succ (P.endpoint n) = succ (P.endpoint n) := by
    rw [Ordinal.add_succ]
    exact congrArg succ (Ordinal.principal_add_iff_add_left_eq_self.mp (P.principal n) _
      (P.boundary_nat_lt n))
  change P.boundary ((n+1 : ℕ) : Ordinal) - P.boundary (n : Ordinal) = _
  rw [P.boundary_succ]
  calc
    _ = (P.boundary (n : Ordinal) + succ (P.endpoint n)) - P.boundary (n : Ordinal) := by rw [ha]
    _ = succ (P.endpoint n) := Ordinal.add_sub_cancel _ _

theorem blockMap_infinite_blocks (ξ : Iio (Ordinal.omega0 : Ordinal.{u})) :
    Ordinal.omega0 ≤ JLMS.ordinalSpaceBlockLength P.blockMap ξ := by
  obtain ⟨n, hn⟩ := ordinalOmegaNatIndexEquiv.surjective ξ
  rw [← hn, P.blockMap_length]
  exact (P.head_large.le.trans (P.strictMono.monotone (Nat.zero_le n))).trans (Order.le_succ _)

end OrdinalPrincipalCofinalSequence
end Posets
