import JLMS.OrdinalSpaceBlocksTopology
import Mathlib.SetTheory.Ordinal.Topology

/-! Independent normal selectors in consecutive ordinal blocks glue to a
normal map.  In particular the junctions, including limit junctions, are
retained.  The resulting range is a closed ordinal copy rather than the
one-point compactification of a disjoint family of blocks. -/

noncomputable section
namespace Posets
open Ordinal
universe u

def ordinalBlockwiseSelector (κ : Ordinal.{u})
    (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) : Ordinal.{u} :=
  κ * (x / κ) + f (x / κ) (x % κ)

theorem ordinalBlockwiseSelector_block {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) (q : Ordinal.{u})
    {r : Ordinal.{u}} (hr : r < κ) :
    ordinalBlockwiseSelector κ f (κ * q + r) = κ * q + f q r := by
  simp only [ordinalBlockwiseSelector, Ordinal.mul_add_div q hκ, Ordinal.div_eq_zero_of_lt hr,
    add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

theorem ordinalBlockwiseSelector_junction {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) (hzero : ∀ q, f q 0 = 0)
    (q : Ordinal.{u}) : ordinalBlockwiseSelector κ f (κ * q) = κ * q := by
  simpa only [add_zero, hzero] using
    ordinalBlockwiseSelector_block hκ f q (Ordinal.pos_iff_ne_zero.mpr hκ)

theorem ordinalBlockwiseSelector_strictMono {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ q, Ordinal.IsNormal (f q)) (htop : ∀ q, f q κ = κ) :
    StrictMono (ordinalBlockwiseSelector κ f) := by
  intro x y hxy
  have hq : x / κ ≤ y / κ := Ordinal.div_le_left hxy.le κ
  rcases hq.eq_or_lt with heq | hlt
  · have hr : x % κ < y % κ := by
      apply (add_lt_add_iff_left (κ * (y / κ))).mp
      calc
        κ * (y / κ) + x % κ = x := by rw [← heq, Ordinal.div_add_mod]
        _ < y := hxy
        _ = κ * (y / κ) + y % κ := (Ordinal.div_add_mod y κ).symm
    change κ * (x / κ) + f (x / κ) (x % κ) <
      κ * (y / κ) + f (y / κ) (y % κ)
    rw [heq]
    exact add_lt_add_left ((hf _).strictMono hr) _
  · have hr : f (x / κ) (x % κ) < κ := by
      simpa only [htop] using (hf (x / κ)).strictMono (Ordinal.mod_lt x hκ)
    calc
      ordinalBlockwiseSelector κ f x < κ * (x / κ) + κ := add_lt_add_left hr _
      _ = κ * Order.succ (x / κ) := (Ordinal.mul_succ _ _).symm
      _ ≤ κ * (y / κ) := mul_le_mul_left' (Order.succ_le_of_lt hlt) _
      _ ≤ ordinalBlockwiseSelector κ f y := Ordinal.le_add_right _ _

theorem ordinalBlockwiseSelector_isNormal {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ q, Ordinal.IsNormal (f q)) (hzero : ∀ q, f q 0 = 0)
    (htop : ∀ q, f q κ = κ) : Ordinal.IsNormal (ordinalBlockwiseSelector κ f) := by
  refine (Ordinal.isNormal_iff_strictMono_limit _).mpr
    ⟨ordinalBlockwiseSelector_strictMono hκ f hf htop, ?_⟩
  intro x hx a ha
  have hid (y : Ordinal.{u}) : y ≤ ordinalBlockwiseSelector κ f y := by
    calc
      y = κ * (y / κ) + y % κ := (Ordinal.div_add_mod y κ).symm
      _ ≤ κ * (y / κ) + f (y / κ) (y % κ) := add_le_add_left (hf _).le_apply _
  by_cases hr : x % κ = 0
  · have hxfix : ordinalBlockwiseSelector κ f x = x := by
      change κ * (x / κ) + f (x / κ) (x % κ) = x
      rw [hr, hzero]
      simpa only [hr] using Ordinal.div_add_mod x κ
    rw [hxfix]
    exact hx.le_iff_forall_le.mpr (fun y hy => (hid y).trans (ha y hy))
  · have hrlim : Order.IsSuccLimit (x % κ) := by
      have h := hx
      rw [← Ordinal.div_add_mod x κ, Ordinal.isSuccLimit_add_iff] at h
      exact h.resolve_right (fun h => hr h.1)
    have hnormal := (Ordinal.isNormal_add_right (κ * (x / κ))).comp (hf (x / κ))
    apply (hnormal.le_iff_forall_le hrlim).mpr
    intro r hrx
    have hrκ : r < κ := hrx.trans (Ordinal.mod_lt x hκ)
    have hprev : κ * (x / κ) + r < x := by
      simpa only [Ordinal.div_add_mod] using add_lt_add_left hrx (κ * (x / κ))
    have h := ha _ hprev
    rwa [ordinalBlockwiseSelector_block hκ f _ hrκ] at h

def ordinalBlockwiseContinuousMap {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (η : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ q, Ordinal.IsNormal (f q)) (hzero : ∀ q, f q 0 = 0)
    (htop : ∀ q, f q κ = κ) :
    C(JLMS.OrdinalInterval (κ * η), JLMS.OrdinalInterval (κ * η)) where
  toFun x := ⟨ordinalBlockwiseSelector κ f x.val, Ordinal.zero_le _, by
    have h := (ordinalBlockwiseSelector_isNormal hκ f hf hzero htop).monotone x.property.2
    rwa [ordinalBlockwiseSelector_junction hκ f hzero] at h⟩
  continuous_toFun := ((ordinalBlockwiseSelector_isNormal hκ f hf hzero htop).continuous.comp
    continuous_subtype_val).subtype_mk _

theorem ordinalBlockwiseContinuousMap_strictMono {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (η : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ q, Ordinal.IsNormal (f q)) (hzero : ∀ q, f q 0 = 0)
    (htop : ∀ q, f q κ = κ) :
    StrictMono (ordinalBlockwiseContinuousMap hκ η f hf hzero htop) :=
  fun _ _ h => ordinalBlockwiseSelector_strictMono hκ f hf htop h

@[simp] theorem ordinalBlockwiseContinuousMap_endpoint {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (η : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ q, Ordinal.IsNormal (f q)) (hzero : ∀ q, f q 0 = 0)
    (htop : ∀ q, f q κ = κ) :
    ordinalBlockwiseContinuousMap hκ η f hf hzero htop
      ⟨κ * η, Ordinal.zero_le _, le_rfl⟩ = ⟨κ * η, Ordinal.zero_le _, le_rfl⟩ :=
  Subtype.ext (ordinalBlockwiseSelector_junction hκ f hzero η)

theorem ordinalBlockwiseContinuousMap_range_closed {κ : Ordinal.{u}} (hκ : κ ≠ 0)
    (η : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u} → Ordinal.{u})
    (hf : ∀ q, Ordinal.IsNormal (f q)) (hzero : ∀ q, f q 0 = 0)
    (htop : ∀ q, f q κ = κ) :
    IsClosed (Set.range (ordinalBlockwiseContinuousMap hκ η f hf hzero htop)) :=
  (ordinalBlockwiseContinuousMap hκ η f hf hzero htop).continuous.isClosedMap.isClosed_range

end Posets
