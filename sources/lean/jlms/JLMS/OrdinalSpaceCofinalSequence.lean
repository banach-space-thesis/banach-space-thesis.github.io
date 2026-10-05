import JLMS.OrdinalScattered
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Continuous cofinal exponent sequences

For a limit ordinal γ we complete a fundamental sequence of length cof(γ)
to a normal function. The value at zero is two, each successor value is
a successor ordinal, and the value at cof(γ) is exactly γ. These are the
exponent sequences used in the limit step of Kislyakov's Corollary 3.2.

The completion uses initial suprema rather than a recursive definition:
after extending the fundamental sequence to a strictly increasing global
function g, set h(ξ)=2+sup_{η<ξ}(g(η)+1).
-/

noncomputable section
namespace JLMS
open Order
universe u

/-- The supremum of the successors of the preceding values. -/
def ordinalInitialSup (f : Ordinal.{u} → Ordinal.{u}) (ξ : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.blsub ξ (fun η _ => f η)

theorem ordinalInitialSup_isNormal (f : Ordinal.{u} → Ordinal.{u}) (hf : StrictMono f) :
    Ordinal.IsNormal (ordinalInitialSup f) := by
  apply (Ordinal.isNormal_iff_strictMono_limit _).mpr
  constructor
  · intro ξ η hξη
    exact (Ordinal.blsub_le (fun ζ hζ => hf hζ)).trans_lt
      (Ordinal.lt_blsub (fun ζ _ => f ζ) ξ hξη)
  · intro ξ hξ a ha
    apply Ordinal.blsub_le
    intro η hη
    exact (Ordinal.lt_blsub (fun ζ _ => f ζ) η (Order.lt_succ η)).trans_le
      (ha (Order.succ η) (hξ.succ_lt hη))

@[simp] theorem ordinalInitialSup_zero (f : Ordinal.{u} → Ordinal.{u}) :
    ordinalInitialSup f 0 = 0 := Ordinal.blsub_zero _

theorem ordinalInitialSup_succ (f : Ordinal.{u} → Ordinal.{u}) (hf : Monotone f)
    (ξ : Ordinal.{u}) : ordinalInitialSup f (Order.succ ξ) = Order.succ (f ξ) :=
  Ordinal.blsub_succ_of_mono (fun _ _ h => hf h)

/-- Extend a fundamental sequence beyond its index ordinal without losing strictness. -/
def ordinalFundamentalExtension (γ : Ordinal.{u})
    (f : ∀ ξ < γ.cof.ord, Ordinal.{u}) (ξ : Ordinal.{u}) : Ordinal.{u} :=
  if hξ : ξ < γ.cof.ord then f ξ hξ else γ + ξ

theorem ordinalFundamentalExtension_strictMono (γ : Ordinal.{u})
    (f : ∀ ξ < γ.cof.ord, Ordinal.{u}) (hf : Ordinal.IsFundamentalSequence γ γ.cof.ord f) :
    StrictMono (ordinalFundamentalExtension γ f) := by
  intro ξ η hξη
  by_cases hη : η < γ.cof.ord
  · have hξ := hξη.trans hη
    simp only [ordinalFundamentalExtension, dif_pos hξ, dif_pos hη]
    exact hf.strict_mono hξ hη hξη
  · by_cases hξ : ξ < γ.cof.ord
    · simp only [ordinalFundamentalExtension, dif_pos hξ, dif_neg hη]
      exact (hf.lt hξ).trans_le (Ordinal.le_add_right γ η)
    · simp only [ordinalFundamentalExtension, dif_neg hξ, dif_neg hη]
      exact (Ordinal.isNormal_add_right γ).strictMono hξη

def ordinalCofinalExponent (γ : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  fun ξ => 2 + ordinalInitialSup
    (ordinalFundamentalExtension γ (Ordinal.exists_fundamental_sequence γ).choose) ξ

theorem ordinalCofinalExponent_isNormal (γ : Ordinal.{u}) :
    Ordinal.IsNormal (ordinalCofinalExponent γ) :=
  (Ordinal.isNormal_add_right 2).comp
    (ordinalInitialSup_isNormal _ (ordinalFundamentalExtension_strictMono γ _
      (Ordinal.exists_fundamental_sequence γ).choose_spec))

@[simp] theorem ordinalCofinalExponent_zero (γ : Ordinal.{u}) :
    ordinalCofinalExponent γ 0 = 2 := by simp [ordinalCofinalExponent]

theorem two_le_ordinalCofinalExponent (γ ξ : Ordinal.{u}) :
    2 ≤ ordinalCofinalExponent γ ξ := Ordinal.le_add_right _ _

theorem ordinalCofinalExponent_succ (γ ξ : Ordinal.{u}) :
    ordinalCofinalExponent γ (Order.succ ξ) = Order.succ
      (2 + ordinalFundamentalExtension γ (Ordinal.exists_fundamental_sequence γ).choose ξ) := by
  rw [ordinalCofinalExponent, ordinalInitialSup_succ _
    (ordinalFundamentalExtension_strictMono γ _
      (Ordinal.exists_fundamental_sequence γ).choose_spec).monotone, Ordinal.add_succ]

theorem ordinalCofinalExponent_endpoint (γ : Ordinal.{u}) (hγ : IsSuccLimit γ) :
    ordinalCofinalExponent γ γ.cof.ord = γ := by
  have he : ordinalInitialSup
      (ordinalFundamentalExtension γ (Ordinal.exists_fundamental_sequence γ).choose) γ.cof.ord = γ := by
    calc
      _ = Ordinal.blsub γ.cof.ord (Ordinal.exists_fundamental_sequence γ).choose := by
        apply congrArg (Ordinal.blsub γ.cof.ord)
        funext η hη
        exact dif_pos hη
      _ = γ := (Ordinal.exists_fundamental_sequence γ).choose_spec.blsub_eq
  change 2 + _ = γ
  rw [he]
  exact Ordinal.natCast_add_of_omega0_le (Ordinal.omega0_le_of_isSuccLimit hγ) 2

theorem ordinalCofinalExponent_lt (γ : Ordinal.{u}) (hγ : IsSuccLimit γ)
    {ξ : Ordinal.{u}} (hξ : ξ < γ.cof.ord) : ordinalCofinalExponent γ ξ < γ := by
  exact ((ordinalCofinalExponent_isNormal γ).strictMono hξ).trans_eq
    (ordinalCofinalExponent_endpoint γ hγ)

theorem ordinalCofinalExponent_successor_lt (γ : Ordinal.{u}) (hγ : IsSuccLimit γ)
    {ξ : Ordinal.{u}} (hξ : ξ < γ.cof.ord) :
    ordinalCofinalExponent γ (Order.succ ξ) < γ :=
  ordinalCofinalExponent_lt γ hγ
    ((Cardinal.isSuccLimit_ord (Ordinal.aleph0_le_cof.mpr hγ)).succ_lt hξ)

/-- The block exponent is a successor, with predecessor at least two, below γ. -/
theorem ordinalCofinalExponent_successor_data (γ : Ordinal.{u}) (hγ : IsSuccLimit γ)
    {ξ : Ordinal.{u}} (hξ : ξ < γ.cof.ord) :
    ∃ η, 2 ≤ η ∧ Order.succ η < γ ∧
      ordinalCofinalExponent γ (Order.succ ξ) = Order.succ η := by
  refine ⟨_, Ordinal.le_add_right _ _, ?_, ordinalCofinalExponent_succ γ ξ⟩
  rw [← ordinalCofinalExponent_succ]
  exact ordinalCofinalExponent_successor_lt γ hγ hξ

/-- The compact-interval version of the cofinal exponent sequence. -/
def ordinalCofinalExponentMap (γ : Ordinal.{u}) (hγ : IsSuccLimit γ) :
    C(OrdinalInterval γ.cof.ord, OrdinalInterval γ) where
  toFun ξ := ⟨ordinalCofinalExponent γ ξ.val, Ordinal.zero_le _, by
    simpa only [ordinalCofinalExponent_endpoint γ hγ] using
      (ordinalCofinalExponent_isNormal γ).monotone ξ.prop.2⟩
  continuous_toFun :=
    ((ordinalCofinalExponent_isNormal γ).continuous.comp continuous_subtype_val).subtype_mk _

theorem ordinalCofinalExponentMap_strictMono (γ : Ordinal.{u}) (hγ : IsSuccLimit γ) :
    StrictMono (ordinalCofinalExponentMap γ hγ) := by
  intro x y hxy
  exact (ordinalCofinalExponent_isNormal γ).strictMono hxy

@[simp] theorem ordinalCofinalExponentMap_endpoint (γ : Ordinal.{u}) (hγ : IsSuccLimit γ) :
    ordinalCofinalExponentMap γ hγ ⟨γ.cof.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨γ, Ordinal.zero_le _, le_rfl⟩ := Subtype.ext (ordinalCofinalExponent_endpoint γ hγ)

theorem ordinalCofinalExponentMap_successor (γ : Ordinal.{u}) (hγ : IsSuccLimit γ)
    (ξ : Ordinal.{u}) (hξ : ξ < γ.cof.ord) :
    ∃ η, (ordinalCofinalExponentMap γ hγ
      ⟨Order.succ ξ, Ordinal.zero_le _, Order.succ_le_of_lt hξ⟩).val = Order.succ η :=
  ⟨_, ordinalCofinalExponent_succ γ ξ⟩

end JLMS
