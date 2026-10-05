import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# The consecutive natural-number blocks of an ordinal

The interval below `ω * η` is explicitly indexed by a block below `η`
and a natural-number coordinate. Consecutive coordinates correspond to
ordinal successors, as required by the adjacent-absorption construction.
-/

noncomputable section
open Set Ordinal Order
open scoped Ordinal
namespace JLMS
universe u

def ordinalOmegaBlockMap (η : Ordinal.{u}) (p : Iio η × ℕ) : Iio (ω * η) :=
  ⟨ω * p.1.val + p.2, by
    calc
      ω * p.1.val + p.2 < ω * p.1.val + ω :=
        (add_lt_add_iff_left _).2 (Ordinal.nat_lt_omega0 _)
      _ = ω * succ p.1.val := (Ordinal.mul_succ _ _).symm
      _ ≤ ω * η := mul_le_mul_left' (succ_le_iff.2 p.1.property) _⟩

theorem ordinal_omega_mul_add_nat_div (β : Ordinal.{u}) (n : ℕ) :
    (ω * β + n) / ω = β := by
  rw [Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
    Ordinal.div_eq_zero_of_lt (Ordinal.nat_lt_omega0 n), add_zero]

theorem ordinalOmegaBlockMap_bijective (η : Ordinal.{u}) :
    Function.Bijective (ordinalOmegaBlockMap η) := by
  constructor
  · rintro ⟨b, n⟩ ⟨c, m⟩ h
    have heq : ω * b.val + n = ω * c.val + m := congrArg Subtype.val h
    have hb : b = c := Subtype.ext (by
      have hd := congrArg (fun a : Ordinal.{u} => a / ω) heq
      simpa only [ordinal_omega_mul_add_nat_div] using hd)
    subst c
    have hn : n = m := by
      exact_mod_cast (add_left_cancel heq)
    subst m
    rfl
  · intro a
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 (Ordinal.mod_lt a.val Ordinal.omega0_ne_zero)
    let b : Iio η := ⟨a.val / ω, (Ordinal.div_lt Ordinal.omega0_ne_zero).2 a.property⟩
    refine ⟨(b, n), Subtype.ext ?_⟩
    change ω * (a.val / ω) + n = a.val
    rw [← hn, Ordinal.div_add_mod]

/-- The actual consecutive-block reindexing, rather than a cardinality-only equivalence. -/
def ordinalOmegaBlockEquiv (η : Ordinal.{u}) : Iio η × ℕ ≃ Iio (ω * η) :=
  Equiv.ofBijective (ordinalOmegaBlockMap η) (ordinalOmegaBlockMap_bijective η)

@[simp] theorem ordinalOmegaBlockEquiv_apply (η : Ordinal.{u}) (b : Iio η) (n : ℕ) :
    (ordinalOmegaBlockEquiv η (b, n)).val = ω * b.val + n := rfl

theorem ordinalOmegaBlockEquiv_succ (η : Ordinal.{u}) (b : Iio η) (n : ℕ) :
    (ordinalOmegaBlockEquiv η (b, n + 1)).val = succ (ordinalOmegaBlockEquiv η (b, n)).val := by
  change ω * b.val + ((n + 1 : ℕ) : Ordinal) = succ (ω * b.val + n)
  rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Ordinal.add_one_eq_succ]

end JLMS
