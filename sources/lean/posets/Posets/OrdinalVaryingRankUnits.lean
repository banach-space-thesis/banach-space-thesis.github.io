import Posets.OrdinalCofinalBandReadback
import Posets.OrdinalRankUnitBandExtraction
import Mathlib.SetTheory.Ordinal.Principal

/-! Actual cofinal rank units with enough separation for varying finite
source heights.  Additive principality keeps every finite multiple below the
limiting rank, and a recursive successor choice separates adjacent sources. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets

theorem ordinal_mul_nat_lt_of_principal_add {γ ρ : Ordinal.{u}}
    (hγ : Ordinal.Principal (· + ·) γ) (hγ0 : 0 < γ) (hρ : ρ < γ) (n : ℕ) :
    ρ * (n : Ordinal) < γ := by
  induction n with
  | zero => simpa only [Nat.cast_zero, mul_zero] using hγ0
  | succ n ih =>
    rw [Ordinal.natCast_succ, Ordinal.mul_succ]
    exact hγ ih hρ

structure OrdinalVaryingRankUnits (γ : Ordinal.{u}) (s : ℕ → ℕ) where
  unit : ℕ → Iio γ
  infinite : ∀ n, Ordinal.omega0 ≤ (unit n).val
  source_below : ∀ n, (unit n).val * (s n : Ordinal) < γ
  separation : ∀ n, (unit n).val * (s n : Ordinal) < (unit (n+1)).val
  cofinal : ∀ β < γ, ∃ n, β < (unit n).val

theorem exists_ordinalVaryingRankUnits
    (γ : Ordinal.{u}) (hP : Ordinal.Principal (· + ·) γ)
    (hω : Ordinal.omega0 < γ) (hcf : γ.cof = Cardinal.aleph0)
    (s : ℕ → ℕ) : Nonempty (OrdinalVaryingRankUnits γ s) := by
  obtain ⟨a, ha, hcof⟩ := ordinal_cof_aleph0_exists_strictMono_cofinal γ hcf
  have hlim : IsSuccLimit γ :=
    Ordinal.isSuccLimit_of_principal_add (Ordinal.one_lt_omega0.trans hω) hP
  have hγ0 : 0 < γ := Ordinal.omega0_pos.trans hω
  let step (n : ℕ) (r : Iio γ) : Iio γ :=
    ⟨Order.succ (max Ordinal.omega0 (max (a (n+1)).val (r.val * (s n : Ordinal)))),
      hlim.succ_lt (max_lt hω (max_lt (a (n+1)).property
        (ordinal_mul_nat_lt_of_principal_add hP hγ0 r.property (s n))))⟩
  let first : Iio γ := ⟨Order.succ (max Ordinal.omega0 (a 0).val),
    hlim.succ_lt (max_lt hω (a 0).property)⟩
  let r : ℕ → Iio γ := Nat.rec first step
  have hr0 : r 0 = first := rfl
  have hrsucc (n : ℕ) : r (n+1) = step n (r n) := rfl
  have hωr (n : ℕ) : Ordinal.omega0 ≤ (r n).val := by
    cases n with
    | zero => exact (le_max_left _ _).trans (Order.le_succ _)
    | succ n => exact (le_max_left _ _).trans (Order.le_succ _)
  have har (n : ℕ) : (a n).val ≤ (r n).val := by
    cases n with
    | zero => exact (le_max_right _ _).trans (Order.le_succ _)
    | succ n => exact ((le_max_left _ _).trans (le_max_right _ _)).trans (Order.le_succ _)
  exact ⟨{
    unit := r
    infinite := hωr
    source_below := fun n => ordinal_mul_nat_lt_of_principal_add hP hγ0 (r n).property (s n)
    separation := fun n => ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (Order.lt_succ _)
    cofinal := fun β hβ => by
      obtain ⟨n, hn⟩ := hcof β hβ
      exact ⟨n, hn.trans_le (har n)⟩ }⟩

namespace OrdinalVaryingRankUnits

variable {γ : Ordinal.{u}} {s : ℕ → ℕ} (R : OrdinalVaryingRankUnits γ s)

theorem strictMono (hs : ∀ n, 1 ≤ s n) : StrictMono (fun n => (R.unit n).val) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Ordinal.le_mul_left _ (by exact_mod_cast (show 0 < s n by have := hs n; omega))).trans_lt
    (R.separation n)

theorem source_strictMono (hs : ∀ n, 1 ≤ s n) :
    StrictMono (fun n => (R.unit n).val * (s n : Ordinal)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (R.separation n).trans_le
    (Ordinal.le_mul_left _ (by exact_mod_cast (show 0 < s (n+1) by have := hs (n+1); omega)))

theorem target_strictMono (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n) (hds : ∀ n, d n ≤ s n) :
    StrictMono (fun n => (R.unit n).val * (d n : Ordinal)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (mul_le_mul_left' (by exact_mod_cast hds n) _).trans_lt
    ((R.separation n).trans_le
      (Ordinal.le_mul_left _ (by exact_mod_cast (show 0 < d (n+1) by have := hd (n+1); omega))))

theorem target_cofinal (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n) :
    ∀ β < γ, ∃ n, β < (R.unit n).val * (d n : Ordinal) := by
  intro β hβ
  obtain ⟨n, hn⟩ := R.cofinal β hβ
  exact ⟨n, hn.trans_le
    (Ordinal.le_mul_left _ (by exact_mod_cast (show 0 < d n by have := hd n; omega)))⟩

theorem target_below (d : ℕ → ℕ) (hds : ∀ n, d n ≤ s n) (n : ℕ) :
    (R.unit n).val * (d n : Ordinal) < γ :=
  (mul_le_mul_left' (by exact_mod_cast hds n) _).trans_lt (R.source_below n)

theorem power_target_cofinal (hlim : IsSuccLimit γ)
    (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n) :
    ∀ β < Ordinal.omega0 ^ γ, ∃ n, β < Ordinal.omega0 ^ ((R.unit n).val * (d n : Ordinal)) := by
  intro β hβ
  obtain ⟨α, hαγ, hβα⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).mp hβ
  obtain ⟨n, hn⟩ := R.target_cofinal d hd α hαγ
  exact ⟨n, hβα.trans ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn)⟩

theorem power_target_subsequence_cofinal (hlim : IsSuccLimit γ)
    (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n) (hds : ∀ n, d n ≤ s n)
    (k : ℕ → ℕ) (hk : StrictMono k) :
    ∀ β < Ordinal.omega0 ^ γ, ∃ n,
      β < Ordinal.omega0 ^ ((R.unit (k n)).val * (d (k n) : Ordinal)) := by
  intro β hβ
  obtain ⟨n, hn⟩ := R.power_target_cofinal hlim d hd β hβ
  exact ⟨n, hn.trans_le ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone
    ((R.target_strictMono d hd hds).monotone (hk.id_le n)))⟩

end OrdinalVaryingRankUnits
end Posets
