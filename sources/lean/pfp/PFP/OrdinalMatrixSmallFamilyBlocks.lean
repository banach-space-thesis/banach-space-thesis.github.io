import PFP.OrdinalMatrixSmallFamilies
/-!
# Simultaneous blocks for cardinally small families of ordinal operators

Ogden's row/column closure argument works simultaneously for a cardinally small
family. Intersect the closed sets of cuts, then enumerate their common cuts.
This strengthens the single-operator block construction without extra
assumptions, and supports the null-sequence continuity argument.
-/

noncomputable section
namespace Posets.UniverseRegularMatrix
universe ordU
open Posets.UniverseRegularInitial
open JLMS
variable {𝕜 : Type} [RCLike 𝕜] {I : Type ordU} [Nonempty I]
set_option synthInstance.maxSize 4096

def ordinalMatrixSmallFamilyCuts {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{ordU}) : Set Ordinal.{ordU} :=
  {δ | ∀ n, IsOrdinalMatrixCut (T n) τ δ}

theorem isClosed_ordinalMatrixSmallFamilyCuts {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{ordU}) :
    IsClosed (ordinalMatrixSmallFamilyCuts T τ) := by
  have he : ordinalMatrixSmallFamilyCuts T τ = ⋂ n, {δ | IsOrdinalMatrixCut (T n) τ δ} := by
    ext δ
    simp [ordinalMatrixSmallFamilyCuts]
  rw [he]
  exact isClosed_iInter (fun n => isClosed_ordinalMatrixCuts (T n) τ)

theorem not_bddAbove_ordinalMatrixSmallFamilyCuts {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{ordU}) :
    ¬ BddAbove (ordinalMatrixSmallFamilyCuts T τ) := by
  rw [not_bddAbove_iff]
  intro β
  refine ⟨max (max α τ) (Order.succ β), ?_,
    (Order.lt_succ β).trans_le (le_max_right _ _)⟩
  intro n
  refine ⟨(le_max_right α τ).trans (le_max_left _ _), ?_⟩
  intro x y hτ hx hy hyα
  exact False.elim ((not_le_of_gt hyα)
    ((le_max_left α τ).trans ((le_max_left _ _).trans hy)))

theorem exists_initialOrdinalMatrix_smallFamilyCut {c : Cardinal.{ordU}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{ordU})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (β : Ordinal.{ordU}) (hβ : β < c.ord) :
    ∃ δ < c.ord, β < δ ∧ δ ∈ ordinalMatrixSmallFamilyCuts T τ := by
  exact exists_smallIndex_closed_ordinal_above (by simpa only [hc.cof_eq] using hu)
    (by simpa only [hc.cof_eq] using hI)
    (fun n => {δ | IsOrdinalMatrixCut (T n) τ δ})
    (fun n => isClosed_ordinalMatrixCuts (T n) τ)
    (fun n β hβ => exists_initialOrdinalMatrix_cut hc hu (T n) τ hτlt (hτ n) β hβ) β hβ

def ordinalMatrixSmallFamilyBlockMap {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{ordU}) :
    Ordinal.{ordU} → Ordinal.{ordU} := Ordinal.enumOrd (ordinalMatrixSmallFamilyCuts T τ)

theorem isNormal_ordinalMatrixSmallFamilyBlockMap {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{ordU}) :
    Ordinal.IsNormal (ordinalMatrixSmallFamilyBlockMap T τ) :=
  (Ordinal.enumOrd_isNormal_iff_isClosed (not_bddAbove_ordinalMatrixSmallFamilyCuts T τ)).mpr
    (isClosed_ordinalMatrixSmallFamilyCuts T τ)

theorem isOrdinalMatrixCut_smallFamilyBlockMap {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ ν : Ordinal.{ordU}) (n : I) :
    IsOrdinalMatrixCut (T n) τ (ordinalMatrixSmallFamilyBlockMap T τ ν) :=
  Ordinal.enumOrd_mem (not_bddAbove_ordinalMatrixSmallFamilyCuts T τ) ν n

@[simp] theorem ordinalMatrixSmallFamilyBlockMap_zero {α : Ordinal.{ordU}}
    (T : I → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{ordU}) :
    ordinalMatrixSmallFamilyBlockMap T τ 0 = τ := by
  apply le_antisymm _ (isOrdinalMatrixCut_smallFamilyBlockMap T τ 0 (Classical.choice ‹Nonempty I›)).1
  apply Ordinal.enumOrd_le_of_forall_lt
    (show τ ∈ ordinalMatrixSmallFamilyCuts T τ from fun n => isOrdinalMatrixCut_self (T n) τ)
  intro ν hν
  exact (Ordinal.not_lt_zero ν hν).elim

theorem ordinalMatrixSmallFamilyBlockMap_lt {c : Cardinal.{ordU}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{ordU})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (ν : Ordinal.{ordU}) (hν : ν < c.ord) : ordinalMatrixSmallFamilyBlockMap T τ ν < c.ord :=
  enumOrd_lt_of_cofinal_below
    (fun ξ hξ => by simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hξ)
    (exists_initialOrdinalMatrix_smallFamilyCut hc hu hI T τ hτlt hτ) ν hν

@[simp] theorem ordinalMatrixSmallFamilyBlockMap_endpoint {c : Cardinal.{ordU}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{ordU})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    ordinalMatrixSmallFamilyBlockMap T τ c.ord = c.ord := by
  apply le_antisymm _ (isNormal_ordinalMatrixSmallFamilyBlockMap T τ).le_apply
  apply Ordinal.enumOrd_le_of_forall_lt
    (show c.ord ∈ ordinalMatrixSmallFamilyCuts T τ from
      fun _ => ⟨hτlt.le, fun _ _ _ _ hy hyα => False.elim ((not_le_of_gt hyα) hy)⟩)
  exact ordinalMatrixSmallFamilyBlockMap_lt hc hu hI T τ hτlt hτ

def ordinalMatrixSmallFamilyBlockContinuousMap {c : Cardinal.{ordU}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{ordU})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) where
  toFun x := ⟨ordinalMatrixSmallFamilyBlockMap T τ x.val, Ordinal.zero_le _, by
    have h := (isNormal_ordinalMatrixSmallFamilyBlockMap T τ).monotone x.prop.2
    rwa [ordinalMatrixSmallFamilyBlockMap_endpoint hc hu hI T τ hτlt hτ] at h⟩
  continuous_toFun := ((Order.IsNormal.continuous (isNormal_ordinalMatrixSmallFamilyBlockMap T τ)).comp
    continuous_subtype_val).subtype_mk _

theorem strictMono_ordinalMatrixSmallFamilyBlockContinuousMap {c : Cardinal.{ordU}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{ordU})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    StrictMono (ordinalMatrixSmallFamilyBlockContinuousMap hc hu hI T τ hτlt hτ) :=
  fun _ _ hxy => (isNormal_ordinalMatrixSmallFamilyBlockMap T τ).strictMono hxy

@[simp] theorem ordinalMatrixSmallFamilyBlockContinuousMap_endpoint {c : Cardinal.{ordU}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hI : Cardinal.mk I < c)
    (T : I → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{ordU})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    ordinalMatrixSmallFamilyBlockContinuousMap hc hu hI T τ hτlt hτ
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
  Subtype.ext (ordinalMatrixSmallFamilyBlockMap_endpoint hc hu hI T τ hτlt hτ)

end Posets.UniverseRegularMatrix



