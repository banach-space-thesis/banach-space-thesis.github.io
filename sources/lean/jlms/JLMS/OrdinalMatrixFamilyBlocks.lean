import JLMS.OrdinalMatrixBlocks
import JLMS.OrdinalClosedIntersections

/-!
# Simultaneous blocks for countably many ordinal operators

Ogden's row/column closure argument works simultaneously for a countable
family. Intersect the closed sets of cuts, then enumerate their common cuts.
This strengthens the single-operator block construction without extra
assumptions, and supports the null-sequence continuity argument.
-/

noncomputable section
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

def ordinalMatrixFamilyCuts {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) : Set Ordinal.{u} :=
  {δ | ∀ n, IsOrdinalMatrixCut (T n) τ δ}

theorem isClosed_ordinalMatrixFamilyCuts {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    IsClosed (ordinalMatrixFamilyCuts T τ) := by
  have he : ordinalMatrixFamilyCuts T τ = ⋂ n, {δ | IsOrdinalMatrixCut (T n) τ δ} := by
    ext δ
    simp [ordinalMatrixFamilyCuts]
  rw [he]
  exact isClosed_iInter (fun n => isClosed_ordinalMatrixCuts (T n) τ)

theorem not_bddAbove_ordinalMatrixFamilyCuts {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    ¬ BddAbove (ordinalMatrixFamilyCuts T τ) := by
  rw [not_bddAbove_iff]
  intro β
  refine ⟨max (max α τ) (Order.succ β), ?_,
    (Order.lt_succ β).trans_le (le_max_right _ _)⟩
  intro n
  refine ⟨(le_max_right α τ).trans (le_max_left _ _), ?_⟩
  intro x y hτ hx hy hyα
  exact False.elim ((not_le_of_gt hyα)
    ((le_max_left α τ).trans ((le_max_left _ _).trans hy)))

theorem exists_initialOrdinalMatrix_familyCut {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (β : Ordinal.{u}) (hβ : β < c.ord) :
    ∃ δ < c.ord, β < δ ∧ δ ∈ ordinalMatrixFamilyCuts T τ := by
  exact exists_common_closed_ordinal_above (by simpa only [hc.cof_eq] using hu)
    (fun n => {δ | IsOrdinalMatrixCut (T n) τ δ})
    (fun n => isClosed_ordinalMatrixCuts (T n) τ)
    (fun n β hβ => exists_initialOrdinalMatrix_cut hc hu (T n) τ hτlt (hτ n) β hβ) β hβ

def ordinalMatrixFamilyBlockMap {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    Ordinal.{u} → Ordinal.{u} := Ordinal.enumOrd (ordinalMatrixFamilyCuts T τ)

theorem isNormal_ordinalMatrixFamilyBlockMap {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    Ordinal.IsNormal (ordinalMatrixFamilyBlockMap T τ) :=
  (Ordinal.enumOrd_isNormal_iff_isClosed (not_bddAbove_ordinalMatrixFamilyCuts T τ)).mpr
    (isClosed_ordinalMatrixFamilyCuts T τ)

theorem isOrdinalMatrixCut_familyBlockMap {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ ν : Ordinal.{u}) (n : ℕ) :
    IsOrdinalMatrixCut (T n) τ (ordinalMatrixFamilyBlockMap T τ ν) :=
  Ordinal.enumOrd_mem (not_bddAbove_ordinalMatrixFamilyCuts T τ) ν n

@[simp] theorem ordinalMatrixFamilyBlockMap_zero {α : Ordinal.{u}}
    (T : ℕ → OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (τ : Ordinal.{u}) :
    ordinalMatrixFamilyBlockMap T τ 0 = τ := by
  apply le_antisymm _ (isOrdinalMatrixCut_familyBlockMap T τ 0 0).1
  apply Ordinal.enumOrd_le_of_forall_lt
    (show τ ∈ ordinalMatrixFamilyCuts T τ from fun n => isOrdinalMatrixCut_self (T n) τ)
  intro ν hν
  exact (Ordinal.not_lt_zero ν hν).elim

theorem ordinalMatrixFamilyBlockMap_lt {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0)
    (ν : Ordinal.{u}) (hν : ν < c.ord) : ordinalMatrixFamilyBlockMap T τ ν < c.ord :=
  enumOrd_lt_of_cofinal_below
    (fun ξ hξ => by simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hξ)
    (exists_initialOrdinalMatrix_familyCut hc hu T τ hτlt hτ) ν hν

@[simp] theorem ordinalMatrixFamilyBlockMap_endpoint {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    ordinalMatrixFamilyBlockMap T τ c.ord = c.ord := by
  apply le_antisymm _ (isNormal_ordinalMatrixFamilyBlockMap T τ).le_apply
  apply Ordinal.enumOrd_le_of_forall_lt
    (show c.ord ∈ ordinalMatrixFamilyCuts T τ from
      fun _ => ⟨hτlt.le, fun _ _ _ _ hy hyα => False.elim ((not_le_of_gt hyα) hy)⟩)
  exact ordinalMatrixFamilyBlockMap_lt hc hu T τ hτlt hτ

def ordinalMatrixFamilyBlockContinuousMap {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    C(OrdinalInterval c.ord, OrdinalInterval c.ord) where
  toFun x := ⟨ordinalMatrixFamilyBlockMap T τ x.val, Ordinal.zero_le _, by
    have h := (isNormal_ordinalMatrixFamilyBlockMap T τ).monotone x.prop.2
    rwa [ordinalMatrixFamilyBlockMap_endpoint hc hu T τ hτlt hτ] at h⟩
  continuous_toFun := ((Order.IsNormal.continuous (isNormal_ordinalMatrixFamilyBlockMap T τ)).comp
    continuous_subtype_val).subtype_mk _

theorem strictMono_ordinalMatrixFamilyBlockContinuousMap {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    StrictMono (ordinalMatrixFamilyBlockContinuousMap hc hu T τ hτlt hτ) :=
  fun _ _ hxy => (isNormal_ordinalMatrixFamilyBlockMap T τ).strictMono hxy

@[simp] theorem ordinalMatrixFamilyBlockContinuousMap_endpoint {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c)
    (T : ℕ → OrdinalC 𝕜 c.ord →L[𝕜] OrdinalC 𝕜 c.ord) (τ : Ordinal.{u})
    (hτlt : τ < c.ord)
    (hτ : ∀ n (y : OrdinalInterval c.ord), τ ≤ y.val → y.val < c.ord →
      ordinalOperatorMatrix c.ord (T n) ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ y = 0) :
    ordinalMatrixFamilyBlockContinuousMap hc hu T τ hτlt hτ
      ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ = ⟨c.ord, Ordinal.zero_le _, le_rfl⟩ :=
  Subtype.ext (ordinalMatrixFamilyBlockMap_endpoint hc hu T τ hτlt hτ)

end JLMS
