import JLMS.OrdinalSpaceBlocksTopology
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Successor-cardinal block boundaries below a singular initial ordinal

The singular case of Kislyakov's decomposition uses a continuous cofinal
sequence whose successor values are successor initial ordinals. We index it
by the cofinality of the endpoint. This also covers singular fixed points of
the aleph function, where the aleph index need not be below the endpoint.
-/

noncomputable section
namespace JLMS
universe u

/-- Closing a prescribed sequence under larger successor cardinals. -/
def successorCardinalClosure (κ : Cardinal.{u}) (b : Ordinal.{u} → Ordinal.{u})
    (ν : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.limitRecOn ν 0
    (fun ξ prev => (Order.succ (max prev.card (max κ (b ξ).card))).ord)
    (fun ξ _ prev => Ordinal.bsup ξ prev)

@[simp] theorem successorCardinalClosure_zero (κ : Cardinal.{u})
    (b : Ordinal.{u} → Ordinal.{u}) :
    successorCardinalClosure κ b 0 = 0 :=
  Ordinal.limitRecOn_zero ..

@[simp] theorem successorCardinalClosure_succ (κ : Cardinal.{u})
    (b : Ordinal.{u} → Ordinal.{u}) (ν : Ordinal.{u}) :
    successorCardinalClosure κ b (Order.succ ν) =
      (Order.succ (max (successorCardinalClosure κ b ν).card (max κ (b ν).card))).ord :=
  Ordinal.limitRecOn_succ ..

theorem successorCardinalClosure_limit (κ : Cardinal.{u})
    (b : Ordinal.{u} → Ordinal.{u}) {ν : Ordinal.{u}} (hν : Order.IsSuccLimit ν) :
    successorCardinalClosure κ b ν =
      Ordinal.bsup ν (fun ξ _ => successorCardinalClosure κ b ξ) :=
  Ordinal.limitRecOn_limit _ _ _ _ hν

theorem isNormal_successorCardinalClosure (κ : Cardinal.{u})
    (b : Ordinal.{u} → Ordinal.{u}) :
    Ordinal.IsNormal (successorCardinalClosure κ b) := by
  refine Order.IsNormal.of_succ_lt (fun ν => ?_) (@fun ν hν => ?_)
  · rw [successorCardinalClosure_succ, Cardinal.lt_ord]
    exact (le_max_left _ _).trans_lt (Order.lt_succ _)
  · rw [successorCardinalClosure_limit κ b hν]
    constructor
    · rintro _ ⟨ξ, hξ, rfl⟩
      exact Ordinal.le_bsup _ ξ hξ
    · intro a ha
      exact Ordinal.bsup_le (fun ξ hξ => ha ⟨ξ, hξ, rfl⟩)

theorem lt_successorCardinalClosure_succ (κ : Cardinal.{u})
    (b : Ordinal.{u} → Ordinal.{u}) (ν : Ordinal.{u}) :
    b ν < successorCardinalClosure κ b (Order.succ ν) := by
  rw [successorCardinalClosure_succ, Cardinal.lt_ord]
  exact ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (Order.lt_succ _)

theorem lt_successorCardinalClosure (κ : Cardinal.{u})
    (b : Ordinal.{u} → Ordinal.{u}) (ν : Ordinal.{u}) :
    κ.ord < successorCardinalClosure κ b (Order.succ ν) := by
  rw [successorCardinalClosure_succ, Cardinal.ord_lt_ord]
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (Order.lt_succ _)

/-- A singular infinite cardinal is a limit of infinite successor cardinals. -/
theorem succ_lt_singularCardinal {c d : Cardinal.{u}}
    (hc : ¬ c.IsRegular) (hd : Cardinal.aleph0 ≤ d) (hdc : d < c) :
    Order.succ d < c := by
  refine lt_of_le_of_ne (Order.succ_le_of_lt hdc) ?_
  intro he
  exact hc (he ▸ Cardinal.isRegular_succ hd)

theorem successorCardinalClosure_lt {c κ : Cardinal.{u}}
    (hc : ¬ c.IsRegular) (hκ : Cardinal.aleph0 ≤ κ) (hκc : κ < c)
    (b : Ordinal.{u} → Ordinal.{u})
    (hb : ∀ ν < c.ord.cof.ord, b ν < c.ord)
    {ν : Ordinal.{u}} (hν : ν < c.ord.cof.ord) :
    successorCardinalClosure κ b ν < c.ord := by
  induction ν using Ordinal.limitRecOn with
  | zero =>
      rw [successorCardinalClosure_zero, Cardinal.lt_ord, Ordinal.card_zero]
      exact Cardinal.aleph0_pos.trans_le (hκ.trans hκc.le)
  | succ ν ih =>
      have hν' := (Order.lt_succ ν).trans hν
      rw [successorCardinalClosure_succ, Cardinal.ord_lt_ord]
      apply succ_lt_singularCardinal hc
      · exact hκ.trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact max_lt (Cardinal.lt_ord.mp (ih hν'))
          (max_lt hκc (Cardinal.lt_ord.mp (hb ν hν')))
  | limit ν hlim ih =>
      rw [successorCardinalClosure_limit κ b hlim]
      exact Ordinal.bsup_lt_ord (Cardinal.lt_ord.mp hν)
        (fun ξ hξ => ih ξ hξ (hξ.trans hν))

theorem successorCardinalClosure_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    (b : Ordinal.{u} → Ordinal.{u})
    (hb : Ordinal.IsFundamentalSequence c.ord c.ord.cof.ord (fun ν _ => b ν)) :
    successorCardinalClosure c.ord.cof b c.ord.cof.ord = c.ord := by
  have hκ : Cardinal.aleph0 ≤ c.ord.cof :=
    Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc)
  have hκc : c.ord.cof < c := lt_of_not_ge (fun h => hs ⟨hc, h⟩)
  have hlim := Cardinal.isSuccLimit_ord hκ
  apply le_antisymm
  · rw [successorCardinalClosure_limit _ _ hlim]
    exact Ordinal.bsup_le (fun ν hν =>
      (successorCardinalClosure_lt hs hκ hκc b (fun ξ hξ => hb.lt hξ) hν).le)
  · apply hb.blsub_eq ▸ Ordinal.blsub_le ?_
    intro ν hν
    exact (lt_successorCardinalClosure_succ _ b ν).trans_le
      ((isNormal_successorCardinalClosure _ b).monotone (hlim.succ_lt hν).le)

def singularCardinalFundamentalBound (c : Cardinal.{u}) (ν : Ordinal.{u}) : Ordinal.{u} :=
  if h : ν < c.ord.cof.ord then
    Classical.choose (Ordinal.exists_fundamental_sequence c.ord) ν h else 0

theorem isFundamentalSequence_singularCardinalFundamentalBound (c : Cardinal.{u}) :
    Ordinal.IsFundamentalSequence c.ord c.ord.cof.ord
      (fun ν _ => singularCardinalFundamentalBound c ν) := by
  have he : (fun ν (_ : ν < c.ord.cof.ord) => singularCardinalFundamentalBound c ν) =
      Classical.choose (Ordinal.exists_fundamental_sequence c.ord) := by
    funext ν hν
    simp [singularCardinalFundamentalBound, hν]
  rw [he]
  exact Classical.choose_spec (Ordinal.exists_fundamental_sequence c.ord)

/-- The singular endpoint's normal cofinal sequence, beginning at zero. -/
def singularCardinalSequence (c : Cardinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  successorCardinalClosure c.ord.cof (singularCardinalFundamentalBound c)

theorem isNormal_singularCardinalSequence (c : Cardinal.{u}) :
    Ordinal.IsNormal (singularCardinalSequence c) :=
  isNormal_successorCardinalClosure _ _

@[simp] theorem singularCardinalSequence_zero (c : Cardinal.{u}) :
    singularCardinalSequence c 0 = 0 := successorCardinalClosure_zero _ _

theorem singularCardinalSequence_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    singularCardinalSequence c c.ord.cof.ord = c.ord :=
  successorCardinalClosure_endpoint hc hs _
    (isFundamentalSequence_singularCardinalFundamentalBound c)

theorem singularCardinalSequence_lt {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular)
    {ν : Ordinal.{u}} (hν : ν < c.ord.cof.ord) :
    singularCardinalSequence c ν < c.ord := by
  have h := (isNormal_singularCardinalSequence c).strictMono hν
  rwa [singularCardinalSequence_endpoint hc hs] at h

theorem singularCardinalSequence_succ_gt (c : Cardinal.{u}) (ν : Ordinal.{u}) :
    c.ord.cof.ord < singularCardinalSequence c (Order.succ ν) :=
  lt_successorCardinalClosure _ _ _

/-- All successor boundaries are regular successor initial ordinals. -/
theorem singularCardinalSequence_succ_regular {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (ν : Ordinal.{u}) :
    ∃ d : Cardinal.{u}, Cardinal.aleph0 ≤ d ∧
      singularCardinalSequence c (Order.succ ν) = (Order.succ d).ord ∧
        (Order.succ d).IsRegular := by
  let d := max (singularCardinalSequence c ν).card
    (max c.ord.cof (singularCardinalFundamentalBound c ν).card)
  have hd : Cardinal.aleph0 ≤ d :=
    (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  exact ⟨d, hd, successorCardinalClosure_succ _ _ _, Cardinal.isRegular_succ hd⟩

def singularCardinalSequenceMap {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    C(OrdinalInterval c.ord.cof.ord, OrdinalInterval c.ord) where
  toFun x := ⟨singularCardinalSequence c x.val, Ordinal.zero_le _, by
    have h := (isNormal_singularCardinalSequence c).monotone x.prop.2
    rwa [singularCardinalSequence_endpoint hc hs] at h⟩
  continuous_toFun := ((Order.IsNormal.continuous (isNormal_singularCardinalSequence c)).comp
    continuous_subtype_val).subtype_mk _

theorem strictMono_singularCardinalSequenceMap {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    StrictMono (singularCardinalSequenceMap hc hs) :=
  fun _ _ h => (isNormal_singularCardinalSequence c).strictMono h

@[simp] theorem singularCardinalSequenceMap_zero {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    singularCardinalSequenceMap hc hs ⟨0, le_rfl, Ordinal.zero_le _⟩ =
      ⟨0, le_rfl, Ordinal.zero_le _⟩ := by
  apply Subtype.ext
  exact singularCardinalSequence_zero c

@[simp] theorem singularCardinalSequenceMap_endpoint {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) :
    singularCardinalSequenceMap hc hs ⟨c.ord.cof.ord, Ordinal.zero_le _, le_rfl⟩ =
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ := by
  apply Subtype.ext
  exact singularCardinalSequence_endpoint hc hs

/-- The interval between successive boundaries has the order type of its
right endpoint, because that endpoint is a larger infinite initial ordinal. -/
theorem singularCardinalSequenceMap_blockLength {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (ξ : Set.Iio c.ord.cof.ord) :
    ordinalSpaceBlockLength (singularCardinalSequenceMap hc hs) ξ =
      singularCardinalSequence c (Order.succ ξ.val) := by
  change singularCardinalSequence c (Order.succ ξ.val) - singularCardinalSequence c ξ.val = _
  apply Ordinal.sub_eq_of_add_eq
  obtain ⟨d, hd, he, _⟩ := singularCardinalSequence_succ_regular hc ξ.val
  rw [he]
  apply (Ordinal.principal_add_iff_add_left_eq_self.mp
    (Ordinal.principal_add_ord (hd.trans (Order.le_succ d))))
  rw [← he]
  exact (isNormal_singularCardinalSequence c).strictMono (Order.lt_succ _)

theorem singularCardinalSequenceMap_blockLength_infinite {c : Cardinal.{u}}
    (hc : Cardinal.aleph0 ≤ c) (hs : ¬ c.IsRegular) (ξ : Set.Iio c.ord.cof.ord) :
    Ordinal.omega0 ≤ ordinalSpaceBlockLength (singularCardinalSequenceMap hc hs) ξ := by
  rw [singularCardinalSequenceMap_blockLength]
  have hκ : Ordinal.omega0 ≤ c.ord.cof.ord := by
    simpa only [Cardinal.ord_aleph0] using Cardinal.ord_le_ord.mpr
      (Ordinal.aleph0_le_cof.mpr (Cardinal.isSuccLimit_ord hc))
  exact hκ.trans (singularCardinalSequence_succ_gt c ξ.val).le

end JLMS
