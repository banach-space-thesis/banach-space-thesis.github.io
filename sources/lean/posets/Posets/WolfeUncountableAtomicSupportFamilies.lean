import Posets.WolfeUncountableAtomicSupport

/-! One zero-mass tail for a family smaller than the ordinal cofinality.
The common cutoff controls all rows simultaneously and thus can be used at
a stage smaller than a regular uncountable branching cardinal. -/

noncomputable section
open Set
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfeMass_exists_common_zero_ordinal_tail {P : Type u}
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {α : Ordinal.{u}}
    (hα : Cardinal.aleph0 < α.cof) (hP : Cardinal.mk P < α.cof)
    (U : Iio α → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ β < α, ∀ p, wolfeMass M (μ p) (⋃ i : Iio α, ⋃ (_ : β < i.val), U i) = 0 := by
  classical
  choose b hb hz using fun p => wolfeMass_exists_zero_ordinal_tail M (μ p) hα U hU
  refine ⟨⨆ p, b p, Ordinal.iSup_lt_ord hP hb, ?_⟩
  intro p
  apply le_antisymm _ (wolfeMass_nonneg M (μ p) _)
  calc
    wolfeMass M (μ p) (⋃ i : Iio α, ⋃ (_ : (⨆ q, b q) < i.val), U i) ≤
        wolfeMass M (μ p) (⋃ i : Iio α, ⋃ (_ : b p < i.val), U i) := by
      apply wolfeMass_mono M (μ p)
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, (Ordinal.le_iSup b p).trans_lt hi, hxi⟩
    _ = 0 := hz p

theorem wolfeMass_exists_common_zero_regular_tail {P : Type u}
    (M : JLMS.AtomicDualModel 𝕜 K)
    (μ : P → WeakDual 𝕜 (JLMS.CZero 𝕜 K)) {c : Cardinal.{u}}
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hP : Cardinal.mk P < c)
    (U : Iio c.ord → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ β < c.ord, ∀ p,
      wolfeMass M (μ p) (⋃ i : Iio c.ord, ⋃ (_ : β < i.val), U i) = 0 :=
  wolfeMass_exists_common_zero_ordinal_tail M μ
    (by simpa only [hc.cof_eq] using hu) (by simpa only [hc.cof_eq] using hP) U hU

/-- The stage-indexed form avoids making the large subtype `Iio σ` a
small-universe type by hand: its ordinal enumeration supplies that reduction. -/
theorem wolfeMass_exists_stage_zero_ordinal_tail
    (M : JLMS.AtomicDualModel 𝕜 K) {σ α : Ordinal.{u}}
    (μ : Iio σ → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hα : Cardinal.aleph0 < α.cof) (hσ : σ.card < α.cof)
    (U : Iio α → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ β < α, ∀ p, wolfeMass M (μ p) (⋃ i : Iio α, ⋃ (_ : β < i.val), U i) = 0 := by
  let e := Ordinal.enumIsoToType σ
  obtain ⟨β, hβ, hz⟩ := wolfeMass_exists_common_zero_ordinal_tail M
    (fun p : σ.toType => μ (e.symm p)) hα (by simpa only [Cardinal.mk_toType] using hσ) U hU
  refine ⟨β, hβ, ?_⟩
  intro p
  simpa only [e.symm_apply_apply] using hz (e p)

theorem wolfeMass_exists_stage_zero_regular_tail
    (M : JLMS.AtomicDualModel 𝕜 K) {σ : Ordinal.{u}} {c : Cardinal.{u}}
    (μ : Iio σ → WeakDual 𝕜 (JLMS.CZero 𝕜 K))
    (hc : c.IsRegular) (hu : Cardinal.aleph0 < c) (hσ : σ < c.ord)
    (U : Iio c.ord → Set K)
    (hU : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∃ β < c.ord, ∀ p,
      wolfeMass M (μ p) (⋃ i : Iio c.ord, ⋃ (_ : β < i.val), U i) = 0 :=
  wolfeMass_exists_stage_zero_ordinal_tail M μ
    (by simpa only [hc.cof_eq] using hu)
    (by simpa only [hc.cof_eq] using Cardinal.lt_ord.mp hσ) U hU

end Posets
