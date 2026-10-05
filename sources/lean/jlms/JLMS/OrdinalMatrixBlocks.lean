import JLMS.OrdinalOrdinaryColumnTail
import JLMS.OrdinalMatrixAlgebra
import Mathlib.SetTheory.Ordinal.Topology

/-!
# Ogden's block boundaries

A cut separates all matrix entries in both directions, after an initial head.
The row support bounds and the endpoint continuity of ordinary columns allow
successive closure under rows and columns. A countable iteration gives a new
cut below the regular uncountable endpoint. The set of cuts is closed, so its
ordinal enumeration supplies the continuous increasing block map of Lemma 4.7.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

/-- A boundary across which both off-diagonal rectangles vanish. -/
def IsOrdinalMatrixCut {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ δ : Ordinal.{u}) : Prop :=
  τ ≤ δ ∧ ∀ x y : OrdinalInterval α, τ ≤ x.val → x.val < δ →
    δ ≤ y.val → y.val < α →
    ordinalOperatorMatrix α T x y = 0 ∧ ordinalOperatorMatrix α T y x = 0

theorem isOrdinalMatrixCut_self {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    IsOrdinalMatrixCut T τ τ :=
  ⟨le_rfl, fun _ _ hτ hx _ _ => False.elim ((not_lt_of_ge hτ) hx)⟩

theorem isClosed_ordinalMatrixCuts {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    IsClosed {δ | IsOrdinalMatrixCut T τ δ} := by
  apply Ordinal.isClosed_iff_iSup.mpr
  intro ι hι f hf
  let i := Classical.choice hι
  refine ⟨(hf i).1.trans (Ordinal.le_iSup f i), ?_⟩
  intro x y hτ hx hy hyα
  obtain ⟨j, hj⟩ := Ordinal.lt_iSup_iff.mp hx
  exact (hf j).2 x y hτ hj ((Ordinal.le_iSup f j).trans hy) hyα

theorem not_bddAbove_ordinalMatrixCuts {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    ¬ BddAbove {δ | IsOrdinalMatrixCut T τ δ} := by
  rw [not_bddAbove_iff]
  intro β
  refine ⟨max (max α τ) (Order.succ β), ⟨?_, ?_⟩, ?_⟩
  · exact (le_max_right α τ).trans (le_max_left _ _)
  · intro x y hτ hx hy hyα
    exact False.elim ((not_le_of_gt hyα)
      ((le_max_left α τ).trans ((le_max_left _ _).trans hy)))
  · exact (Order.lt_succ β).trans_le (le_max_right _ _)

/-- One stage of closing an initial rectangle under matrix rows and columns. -/
theorem exists_initialOrdinalMatrix_rectangleCutoff {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (β : Ordinal.{u}) (hβ : β < c.ord) :
    ∃ γ < c.ord, β < γ ∧ ∀ x y : OrdinalInterval c.ord,
      x.val < β → γ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T x y = 0 ∧
        (τ ≤ x.val → ordinalOperatorMatrix c.ord T y x = 0) := by
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  have hβcard : β.card < c.ord.cof := by
    simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hβ
  obtain ⟨ρ, hρ, hrow⟩ := exists_uniform_ordinal_ellOne_cutoff hcf hβcard
    (fun x hx => ordinalOperatorRow c.ord T ⟨x, Ordinal.zero_le _, (hx.trans hβ).le⟩)
  have hcols (ν : Ordinal.{u}) (hν : ν < β) :=
    exists_initialOrdinalOrdinaryColumn_tail hc hu T ν (hν.trans hβ)
  choose b hb hcol using hcols
  let σ := Ordinal.bsup β b
  have hσ : σ < c.ord := Ordinal.bsup_lt_ord hβcard hb
  let γ := Order.succ (max β (max ρ σ))
  have hγ : γ < c.ord := (Ordinal.aleph0_le_cof.mp hcf.le).succ_lt
    (max_lt hβ (max_lt hρ hσ))
  have hργ : ρ < γ := (le_max_left ρ σ).trans
    (le_max_right β (max ρ σ)) |>.trans_lt (Order.lt_succ _)
  have hσγ : σ < γ := (le_max_right ρ σ).trans
    (le_max_right β (max ρ σ)) |>.trans_lt (Order.lt_succ _)
  refine ⟨γ, hγ, (le_max_left β (max ρ σ)).trans_lt (Order.lt_succ _), ?_⟩
  intro x y hx hy hyα
  constructor
  · exact hrow x.val hx y (hργ.trans_le hy) hyα
  · intro hτx
    have he := hcol x.val hx y
      ((Ordinal.le_bsup b x.val hx).trans_lt (hσγ.trans_le hy))
    exact he.trans (hτ x hτx (hx.trans hβ))

/-- The row/column closure of any bounded head remains below the endpoint. -/
theorem exists_initialOrdinalMatrix_cut {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (β : Ordinal.{u}) (hβ : β < c.ord) :
    ∃ δ < c.ord, β < δ ∧ IsOrdinalMatrixCut T τ δ := by
  have hcf : Cardinal.aleph0 < c.ord.cof := by simpa only [hc.cof_eq] using hu
  let step (a : Set.Iio c.ord) : Set.Iio c.ord :=
    ⟨Classical.choose (exists_initialOrdinalMatrix_rectangleCutoff hc hu T τ hτ a.val a.prop),
      (Classical.choose_spec
        (exists_initialOrdinalMatrix_rectangleCutoff hc hu T τ hτ a.val a.prop)).1⟩
  have hstep (a : Set.Iio c.ord) : a.val < (step a).val ∧
      ∀ x y : OrdinalInterval c.ord, x.val < a.val → (step a).val ≤ y.val →
        y.val < c.ord → ordinalOperatorMatrix c.ord T x y = 0 ∧
          (τ ≤ x.val → ordinalOperatorMatrix c.ord T y x = 0) :=
    (Classical.choose_spec
      (exists_initialOrdinalMatrix_rectangleCutoff hc hu T τ hτ a.val a.prop)).2
  let initial : Set.Iio c.ord := ⟨max τ β, max_lt hτlt hβ⟩
  let a (n : ℕ) := step^[n] initial
  let b (n : ℕ) := (a n).val
  have hb (n : ℕ) : b n < c.ord := (a n).prop
  have hnext (n : ℕ) : a (n + 1) = step (a n) := Function.iterate_succ_apply' step n initial
  let δ := ⨆ n, b n
  have hδ : δ < c.ord := Ordinal.iSup_lt_ord_lift (by simpa using hcf) hb
  have hτδ : τ ≤ δ := (le_max_left τ β).trans (Ordinal.le_iSup b 0)
  have hβδ : β < δ := (le_max_right τ β).trans_lt
    ((hstep initial).1.trans_le (by simpa only [b, hnext] using Ordinal.le_iSup b 1))
  refine ⟨δ, hδ, hβδ, hτδ, ?_⟩
  intro x y hτx hx hy hyα
  obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hx
  have hnnext : (step (a n)).val ≤ y.val := by
    rw [← hnext]
    exact (Ordinal.le_iSup b (n + 1)).trans hy
  have hz := (hstep (a n)).2 x y hn hnnext hyα
  exact ⟨hz.1, hz.2 hτx⟩

/-- The normal enumeration of all two-sided matrix cuts. -/
def ordinalMatrixBlockMap {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    Ordinal.{u} → Ordinal.{u} :=
  Ordinal.enumOrd {δ | IsOrdinalMatrixCut T τ δ}

theorem isNormal_ordinalMatrixBlockMap {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    Ordinal.IsNormal (ordinalMatrixBlockMap T τ) :=
  (Ordinal.enumOrd_isNormal_iff_isClosed (not_bddAbove_ordinalMatrixCuts T τ)).mpr
    (isClosed_ordinalMatrixCuts T τ)

theorem isOrdinalMatrixCut_blockMap {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ ν : Ordinal.{u}) :
    IsOrdinalMatrixCut T τ (ordinalMatrixBlockMap T τ ν) :=
  Ordinal.enumOrd_mem (not_bddAbove_ordinalMatrixCuts T τ) ν

@[simp] theorem ordinalMatrixBlockMap_zero {α : Ordinal.{u}}
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    ordinalMatrixBlockMap T τ 0 = τ := by
  apply le_antisymm _ (isOrdinalMatrixCut_blockMap T τ 0).1
  apply Ordinal.enumOrd_le_of_forall_lt (isOrdinalMatrixCut_self T τ)
  intro ν hν
  exact (Ordinal.not_lt_zero ν hν).elim

theorem ordinalMatrixBlockMap_lt {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (ν : Ordinal.{u}) (hν : ν < c.ord) : ordinalMatrixBlockMap T τ ν < c.ord := by
  have hall : ∀ ν : Ordinal.{u}, ν < c.ord → ordinalMatrixBlockMap T τ ν < c.ord := by
    intro ν
    induction ν using Ordinal.induction with
    | h ν ih =>
      intro hν
      let b (ξ : Ordinal.{u}) (_ : ξ < ν) := ordinalMatrixBlockMap T τ ξ
      have hνcard : ν.card < c.ord.cof := by
        simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hν
      have hb : Ordinal.bsup ν b < c.ord :=
        Ordinal.bsup_lt_ord hνcard (fun ξ hξ => ih ξ hξ (hξ.trans hν))
      obtain ⟨δ, hδ, hbδ, hcut⟩ :=
        exists_initialOrdinalMatrix_cut hc hu T τ hτlt hτ (Ordinal.bsup ν b) hb
      exact (Ordinal.enumOrd_le_of_forall_lt hcut
        (fun ξ hξ => (Ordinal.le_bsup b ξ hξ).trans_lt hbδ)).trans_lt hδ
  exact hall ν hν

@[simp] theorem ordinalMatrixBlockMap_endpoint {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    ordinalMatrixBlockMap T τ c.ord = c.ord := by
  apply le_antisymm _ (isNormal_ordinalMatrixBlockMap T τ).le_apply
  apply Ordinal.enumOrd_le_of_forall_lt
    (show IsOrdinalMatrixCut T τ c.ord from
      ⟨hτlt.le, fun _ _ _ _ hy hyα => False.elim ((not_le_of_gt hyα) hy)⟩)
  exact ordinalMatrixBlockMap_lt hc hu T τ hτlt hτ

/-- A normal map partitions its final range into consecutive half-open blocks. -/
theorem exists_normal_ordinal_block {f : Ordinal.{u} → Ordinal.{u}}
    (hf : Ordinal.IsNormal f) (x : Ordinal.{u}) (hx : f 0 ≤ x) :
    ∃ ν, f ν ≤ x ∧ x < f (Order.succ ν) := by
  let s : Set Ordinal.{u} := {ν | f ν ≤ x}
  have hs : s.Nonempty := ⟨0, hx⟩
  have hb : BddAbove s := ⟨x, fun ν hν => hf.le_apply.trans hν⟩
  have hclosed : IsClosed s := isClosed_Iic.preimage (Order.IsNormal.continuous hf)
  have hmem : sSup s ∈ s := hclosed.csSup_mem hs hb
  refine ⟨sSup s, hmem, ?_⟩
  by_contra! h
  exact (not_le_of_gt (Order.lt_succ (sSup s))) (le_csSup hb h)

/-- The tail matrix is block diagonal in precisely the sense of Ogden Definition 4.6. -/
theorem ordinalOperatorMatrix_same_block {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (x y : OrdinalInterval c.ord) (hτx : τ ≤ x.val) (hτy : τ ≤ y.val)
    (hx : x.val < c.ord) (hy : y.val < c.ord)
    (hxy : ordinalOperatorMatrix c.ord T x y ≠ 0) :
    ∃ ν < c.ord, ordinalMatrixBlockMap T τ ν ≤ x.val ∧
      x.val < ordinalMatrixBlockMap T τ (Order.succ ν) ∧
      ordinalMatrixBlockMap T τ ν ≤ y.val ∧
      y.val < ordinalMatrixBlockMap T τ (Order.succ ν) := by
  obtain ⟨ν, hνx, hxν⟩ := exists_normal_ordinal_block
    (isNormal_ordinalMatrixBlockMap T τ) x.val (by simpa using hτx)
  have hν : ν < c.ord :=
    ((isNormal_ordinalMatrixBlockMap T τ).le_apply.trans hνx).trans_lt hx
  refine ⟨ν, hν, hνx, hxν, ?_, ?_⟩
  · by_contra! hyν
    exact hxy ((isOrdinalMatrixCut_blockMap T τ ν).2 y x hτy hyν hνx hx).2
  · by_contra! hνy
    exact hxy ((isOrdinalMatrixCut_blockMap T τ (Order.succ ν)).2
      x y hτx hxν hνy hy).1

/-- The continuous interval map underlying the normal block enumeration. -/
def ordinalMatrixBlockContinuousMap {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) where
  toFun x := ⟨ordinalMatrixBlockMap T τ x.val, Ordinal.zero_le _, by
    have h := (isNormal_ordinalMatrixBlockMap T τ).monotone x.prop.2
    rwa [ordinalMatrixBlockMap_endpoint hc hu T τ hτlt hτ] at h⟩
  continuous_toFun := ((Order.IsNormal.continuous (isNormal_ordinalMatrixBlockMap T τ)).comp
    continuous_subtype_val).subtype_mk _

theorem strictMono_ordinalMatrixBlockContinuousMap {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ y : OrdinalInterval c.ord, τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord T ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    StrictMono (ordinalMatrixBlockContinuousMap hc hu T τ hτlt hτ) :=
  fun _ _ hxy => (isNormal_ordinalMatrixBlockMap T τ).strictMono hxy

end JLMS
