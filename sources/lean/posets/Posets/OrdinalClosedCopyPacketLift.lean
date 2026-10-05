import Posets.OrdinalClosedCopyPackets

/-! Universe-compatible packet bounds for subsets of ordinal spaces. -/

noncomputable section
open Set
universe u
namespace Posets

theorem ordinal_lift_finite_power (κ : Ordinal.{u}) (n : ℕ) :
    Ordinal.lift.{u+1} (κ ^ (n : Ordinal)) =
      (Ordinal.lift.{u+1} κ) ^ (n : Ordinal) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one, Ordinal.add_one_eq_succ,
        Ordinal.opow_succ, Ordinal.lift_mul] using congrArg (fun x => x * Ordinal.lift.{u+1} κ) ih

theorem ordinal_isRegular_lift {c : Cardinal.{u}} (hc : c.IsRegular) :
    (Cardinal.lift.{u+1} c).IsRegular := by
  constructor
  · simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.mpr hc.aleph0_le
  · rw [← Cardinal.lift_ord, ← Ordinal.lift_cof]
    exact Cardinal.lift_le.mpr hc.2

theorem ordinal_type_le_of_regular_packets_lift
    {X : Type (u+1)} [LinearOrder X] [WellFoundedLT X]
    {c : Cardinal.{u}} (hc : c.IsRegular) (n : ℕ)
    (f : X → Ordinal.{u}) (hf : Monotone f) (β : Ordinal.{u})
    (hbound : ∀ x, f x < c.ord * β)
    (hF : ∀ y, Ordinal.type (· < · : {x : X // f x = y} → _ → Prop) <
      Ordinal.lift.{u+1} (c.ord ^ (n + 1 : Ordinal))) :
    Ordinal.type (· < · : X → _ → Prop) ≤
      Ordinal.lift.{u+1} (c.ord ^ (n + 1 : Ordinal) * β) := by
  classical
  let g (x : X) : Ordinal.{u+1} := Ordinal.lift.{u+1} (f x)
  have hg : Monotone g := fun _ _ h => Ordinal.lift_le.mpr (hf h)
  have hp : (Cardinal.lift.{u+1} c).ord ^ (n + 1 : Ordinal) =
      Ordinal.lift.{u+1} (c.ord ^ (n + 1 : Ordinal)) := by
    rw [← Cardinal.lift_ord]
    exact (ordinal_lift_finite_power c.ord (n+1)).symm
  have hsmall (y : Ordinal.{u+1}) :
      Ordinal.type (· < · : {x : X // g x = y} → _ → Prop) <
        (Cardinal.lift.{u+1} c).ord ^ (n + 1 : Ordinal) := by
    rw [hp]
    let F := {x : X // g x = y}
    by_cases hn : Nonempty F
    · obtain ⟨x₀⟩ := hn
      let e (x : F) : {x : X // f x = f x₀.val} :=
        ⟨x.val, Ordinal.lift_inj.mp (x.property.trans x₀.property.symm)⟩
      have he : StrictMono e := fun _ _ h => h
      exact (RelEmbedding.ofMonotone e he).ordinal_type_le.trans_lt (hF _)
    · letI : IsEmpty F := not_nonempty_iff.mp hn
      rw [Ordinal.type_eq_zero_iff_isEmpty.mpr inferInstance]
      simpa only [Ordinal.lift_zero] using
        (Ordinal.lift_lt.mpr (Ordinal.opow_pos (n + 1 : Ordinal) hc.ord_pos))
  have h := ordinal_type_le_of_regular_packets (ordinal_isRegular_lift hc) n
    g hg (Ordinal.lift.{u+1} β) (fun x => ?_) hsmall
  · simpa only [hp, ← Ordinal.lift_mul] using h
  · change Ordinal.lift.{u+1} (f x) < _
    rw [← Cardinal.lift_ord, ← Ordinal.lift_mul]
    exact Ordinal.lift_lt.mpr (hbound x)

end Posets
