import Posets.OrdinalJumpedCofinalSelection
import Posets.OrdinalPrincipalTransfiniteSequence
import Posets.OrdinalTransfiniteRankUnits

/-! A genuine cofinal block sequence extracted from the literal injection
of selected coloured cores.  The chosen reindex preserves those actual
cores; all remaining fields concern ordinal geometry only. -/

noncomputable section
open Set Order
namespace Posets

structure OrdinalTransfiniteTargetSelection {c : Cardinal.{0}} {Γ : Ordinal.{0}}
    (P : OrdinalPrincipalTransfiniteSequence c.ord Γ) (k : Iio c.ord → Iio c.ord) where
  reindex : Iio c.ord → Iio c.ord
  injective : Function.Injective reindex
  index_strictMono : StrictMono (k ∘ reindex)
  index_growth : ∀ i, i < k (reindex i)
  sequence : OrdinalPrincipalTransfiniteSequence c.ord Γ
  endpoint_eq : ∀ i, sequence.endpoint i = P.endpoint (k (reindex i))

namespace OrdinalPrincipalTransfiniteSequence
variable {c : Cardinal.{0}} {Γ : Ordinal.{0}}
  (P : OrdinalPrincipalTransfiniteSequence c.ord Γ)

theorem exists_targetSelection (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    Nonempty (OrdinalTransfiniteTargetSelection P k) := by
  have hpositive (i : Iio c.ord) : P.endpoint i ≠ 0 := by
    apply ne_of_gt
    exact ((Ordinal.zero_le c.ord).trans_lt P.head_large).trans_le
      (P.strictMono.monotone (show P.zeroIndex ≤ i from Ordinal.zero_le i.val))
  obtain ⟨r, hr, hkr, hi, _, hgap⟩ :=
    exists_regularOrdinal_injective_principal_gap_selection hc P.endpoint
      P.strictMono P.principal hpositive k hk
  let Q : OrdinalPrincipalTransfiniteSequence c.ord Γ := {
    infinite := P.infinite
    endpoint := fun i => P.endpoint (k (r i))
    strictMono := P.strictMono.comp hkr
    principal := fun i => P.principal (k (r i))
    head_large := P.head_large.trans_le (P.strictMono.monotone
      (show P.zeroIndex ≤ k (r P.zeroIndex) from Ordinal.zero_le _))
    bound := fun i => P.bound (k (r i))
    cofinal := fun β hβ => by
      obtain ⟨i, hβi⟩ := P.cofinal β hβ
      exact ⟨i, hβi.trans_le (P.strictMono.monotone (hi i).le)⟩
    gap := hgap }
  exact ⟨⟨r, hr, hkr, hi, Q, fun _ => rfl⟩⟩

def targetSelection (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    OrdinalTransfiniteTargetSelection P k := Classical.choice (P.exists_targetSelection hc k hk)

def selectedTargetReindex (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) : Iio c.ord → Iio c.ord :=
  (P.targetSelection hc k hk).reindex

def selectedTargetSequence (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    OrdinalPrincipalTransfiniteSequence c.ord Γ := (P.targetSelection hc k hk).sequence

theorem selectedTargetReindex_injective (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    Function.Injective (P.selectedTargetReindex hc k hk) :=
  (P.targetSelection hc k hk).injective

theorem selectedTargetIndex_strictMono (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    StrictMono (k ∘ P.selectedTargetReindex hc k hk) :=
  (P.targetSelection hc k hk).index_strictMono

@[simp] theorem selectedTargetSequence_endpoint (hc : c.IsRegular)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) (i : Iio c.ord) :
    (P.selectedTargetSequence hc k hk).endpoint i =
      P.endpoint (k (P.selectedTargetReindex hc k hk i)) :=
  (P.targetSelection hc k hk).endpoint_eq i

end OrdinalPrincipalTransfiniteSequence

namespace OrdinalTransfiniteRankUnits
variable {c : Cardinal.{0}} {γ : Ordinal.{0}} {s : ℕ}
  (R : OrdinalTransfiniteRankUnits c.ord γ s)

def selectedTargetReindex (hc : c.IsRegular) (hs : 0 < s) (hγ : IsSuccLimit γ)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) : Iio c.ord → Iio c.ord :=
  (R.baseTargetSequence hs hγ).selectedTargetReindex hc k hk

def selectedTargetSequence (hc : c.IsRegular) (hs : 0 < s) (hγ : IsSuccLimit γ)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    OrdinalPrincipalTransfiniteSequence c.ord (Ordinal.omega0 ^ γ) :=
  (R.baseTargetSequence hs hγ).selectedTargetSequence hc k hk

theorem selectedTargetReindex_injective (hc : c.IsRegular) (hs : 0 < s) (hγ : IsSuccLimit γ)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    Function.Injective (R.selectedTargetReindex hc hs hγ k hk) :=
  (R.baseTargetSequence hs hγ).selectedTargetReindex_injective hc k hk

theorem selectedTargetIndex_strictMono (hc : c.IsRegular) (hs : 0 < s) (hγ : IsSuccLimit γ)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    StrictMono (k ∘ R.selectedTargetReindex hc hs hγ k hk) :=
  (R.baseTargetSequence hs hγ).selectedTargetIndex_strictMono hc k hk

theorem selectedTargetIndex_growth (hc : c.IsRegular) (hs : 0 < s) (hγ : IsSuccLimit γ)
    (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) (i : Iio c.ord) :
    i < k (R.selectedTargetReindex hc hs hγ k hk i) :=
  ((R.baseTargetSequence hs hγ).targetSelection hc k hk).index_growth i

@[simp] theorem selectedTargetSequence_endpoint (hc : c.IsRegular) (hs : 0 < s)
    (hγ : IsSuccLimit γ) (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k)
    (i : Iio c.ord) :
    (R.selectedTargetSequence hc hs hγ k hk).endpoint i =
      Ordinal.omega0 ^ R.unit (k (R.selectedTargetReindex hc hs hγ k hk i)) :=
  ((R.baseTargetSequence hs hγ).targetSelection hc k hk).endpoint_eq i

theorem selectedTargetUnit_cofinal (hc : c.IsRegular) (hs : 0 < s)
    (hγ : IsSuccLimit γ) (k : Iio c.ord → Iio c.ord) (hk : Function.Injective k) :
    ∀ β < γ, ∃ i, β < R.unit (k (R.selectedTargetReindex hc hs hγ k hk i)) := by
  intro β hβ
  obtain ⟨i, hi⟩ := R.cofinal β hβ
  exact ⟨i, hi.trans_le (R.strictMono.monotone
    (R.selectedTargetIndex_growth hc hs hγ k hk i).le)⟩

end OrdinalTransfiniteRankUnits
end Posets

