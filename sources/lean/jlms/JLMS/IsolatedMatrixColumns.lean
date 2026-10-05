import JLMS.OrdinalAtomicMatrix

/-!
# Ogden Proposition 3.4(ii): continuity of isolated-point columns

At an isolated point y, the singleton characteristic function is continuous
and its image under T is precisely the y-column. Zero and successor ordinals
are isolated in their ordinal interval, giving the columns used by Ogden.
-/

noncomputable section
attribute [local instance] Classical.decEq
namespace JLMS
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K]

theorem atomicOperatorMatrix_eq_singletonIndicator (M : AtomicDualModel 𝕜 K)
    (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K) (x y : K) (hy : IsClopen ({y} : Set K)) :
    atomicOperatorMatrix M T x y = T (clopenIndicator {y} hy isCompact_singleton) x := by
  have h := (atomicOperatorRow_hasSum M T (clopenIndicator {y} hy isCompact_singleton) x).tsum_eq
  rw [tsum_eq_single y (fun z hz => by
    simp [clopenIndicator_apply, Set.mem_singleton_iff, hz])] at h
  simpa [clopenIndicator_apply] using h

theorem continuous_atomicOperatorMatrix_column [T1Space K]
    (M : AtomicDualModel 𝕜 K) (T : CZero 𝕜 K →L[𝕜] CZero 𝕜 K)
    (y : K) (hy : IsOpen ({y} : Set K)) :
    Continuous (fun x => atomicOperatorMatrix M T x y) := by
  let hcl : IsClopen ({y} : Set K) := ⟨isClosed_singleton, hy⟩
  convert (T (clopenIndicator {y} hcl isCompact_singleton)).continuous using 1
  funext x
  exact atomicOperatorMatrix_eq_singletonIndicator M T x y hcl

theorem isOpen_singleton_ordinalInterval {α : Ordinal.{u}} (x : OrdinalInterval α)
    (hx : ¬ Order.IsSuccLimit x.val) : IsOpen ({x} : Set (OrdinalInterval α)) := by
  have h := (Ordinal.isOpen_singleton_iff.mpr hx).preimage
    (continuous_subtype_val : Continuous (Subtype.val : OrdinalInterval α → Ordinal.{u}))
  convert h using 1
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact Subtype.ext_iff

theorem continuous_ordinalOperatorMatrix_column (α : Ordinal.{u})
    (T : OrdinalC 𝕜 α →L[𝕜] OrdinalC 𝕜 α) (y : OrdinalInterval α)
    (hy : ¬ Order.IsSuccLimit y.val) :
    Continuous (fun x => ordinalOperatorMatrix α T x y) :=
  continuous_atomicOperatorMatrix_column (ordinalAtomicDualModel α) (ordinalZeroOperator α T)
    y (isOpen_singleton_ordinalInterval y hy)

end JLMS
