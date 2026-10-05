import ThesisCommon.Analysis.InfinityQuotientMasks

/-! Actual contractive restriction and insertion on ℓ∞/c₀ along arbitrary
injections of ℕ. Their split identities hold on every quotient vector. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜]

theorem lpRestrict_mem_cZero (e : ℕ ↪ ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞)
    (hx : x ∈ scalarCZeroSubmodule 𝕜) :
    lpRestrict (𝕜 := 𝕜) ∞ e x ∈ scalarCZeroSubmodule 𝕜 :=
  hx.comp e.injective.tendsto_cofinite

theorem lpExtend_mem_cZero (e : ℕ ↪ ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞)
    (hx : x ∈ scalarCZeroSubmodule 𝕜) :
    lpExtend (𝕜 := 𝕜) ∞ e x ∈ scalarCZeroSubmodule 𝕜 := by
  apply (mem_filterNullSubmodule_iff cofinite _).mpr
  intro ε hε
  have hxε := (mem_filterNullSubmodule_iff cofinite x).mp hx ε hε
  have hfin : {n | ε ≤ ‖x n‖}.Finite := by
    simpa only [Filter.mem_cofinite, Set.compl_setOf, not_lt] using hxε
  apply Filter.mem_cofinite.mpr
  apply (hfin.image e).subset
  intro n hn
  by_cases he : ∃ i, e i = n
  · obtain ⟨i, rfl⟩ := he
    refine ⟨i, ?_, rfl⟩
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, lpExtend_apply_image, not_lt] using hn
  · have hz : lpExtend (𝕜 := 𝕜) ∞ e x n = 0 := by
      change Function.extend e x 0 n = 0
      rw [Function.extend_apply' _ _ _ he]
      rfl
    have hn' : ¬ ‖lpExtend (𝕜 := 𝕜) ∞ e x n‖ < ε := hn
    rw [hz, norm_zero] at hn'
    exact False.elim (hn' hε)

def infinityQuotientRestrict (e : ℕ ↪ ℕ) :
    InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 :=
  quotientMapL (scalarCZeroSubmodule 𝕜) (scalarCZeroSubmodule 𝕜)
    (lpRestrict (𝕜 := 𝕜) ∞ e) (lpRestrict_mem_cZero e)

def infinityQuotientExtend (e : ℕ ↪ ℕ) :
    InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 :=
  quotientMapL (scalarCZeroSubmodule 𝕜) (scalarCZeroSubmodule 𝕜)
    (lpExtend (𝕜 := 𝕜) ∞ e) (lpExtend_mem_cZero e)

@[simp] theorem infinityQuotientRestrict_mk (e : ℕ ↪ ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityQuotientRestrict (𝕜 := 𝕜) e (infinityQuotientMk (𝕜 := 𝕜) x) =
      infinityQuotientMk (𝕜 := 𝕜) (lpRestrict (𝕜 := 𝕜) ∞ e x) := rfl

@[simp] theorem infinityQuotientExtend_mk (e : ℕ ↪ ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityQuotientExtend (𝕜 := 𝕜) e (infinityQuotientMk (𝕜 := 𝕜) x) =
      infinityQuotientMk (𝕜 := 𝕜) (lpExtend (𝕜 := 𝕜) ∞ e x) := rfl

theorem norm_infinityQuotientRestrict_le (e : ℕ ↪ ℕ) :
    ‖infinityQuotientRestrict (𝕜 := 𝕜) e‖ ≤ 1 :=
  (norm_quotientMapL_le _ _ _ _).trans (norm_lpRestrict_le (𝕜 := 𝕜) (X := 𝕜) e)

theorem norm_infinityQuotientExtend_le (e : ℕ ↪ ℕ) :
    ‖infinityQuotientExtend (𝕜 := 𝕜) e‖ ≤ 1 :=
  (norm_quotientMapL_le _ _ _ _).trans (norm_lpExtend_le (𝕜 := 𝕜) (X := 𝕜) e)

theorem infinityQuotientRestrict_comp_extend (e : ℕ ↪ ℕ) :
    (infinityQuotientRestrict (𝕜 := 𝕜) e).comp (infinityQuotientExtend (𝕜 := 𝕜) e) =
      ContinuousLinearMap.id 𝕜 (InfinityCZeroQuotient 𝕜) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    change infinityQuotientMk (𝕜 := 𝕜)
      (lpRestrict (𝕜 := 𝕜) ∞ e (lpExtend (𝕜 := 𝕜) ∞ e x)) = infinityQuotientMk (𝕜 := 𝕜) x
    congr 1
    exact DFunLike.congr_fun (lpRestrict_comp_extend (𝕜 := 𝕜) (p := ∞) e) x

theorem infinityQuotientExtend_comp_restrict (e : ℕ ↪ ℕ) :
    (infinityQuotientExtend (𝕜 := 𝕜) e).comp (infinityQuotientRestrict (𝕜 := 𝕜) e) =
      infinityQuotientMask (𝕜 := 𝕜) (Set.range e) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x =>
    change infinityQuotientMk (𝕜 := 𝕜)
      (lpExtend (𝕜 := 𝕜) ∞ e (lpRestrict (𝕜 := 𝕜) ∞ e x)) =
        infinityQuotientMk (𝕜 := 𝕜) (infinityMask (Set.range e) x)
    congr 1
    apply lp.ext
    funext n
    by_cases hn : n ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hn
      simp
    · rw [infinityMask_apply, if_neg hn]
      change Function.extend e _ 0 n = 0
      rw [Function.extend_apply' _ _ _ hn]
      rfl

theorem infinityQuotientMask_comp_extend (e : ℕ ↪ ℕ) :
    (infinityQuotientMask (𝕜 := 𝕜) (Set.range e)).comp (infinityQuotientExtend (𝕜 := 𝕜) e) =
      infinityQuotientExtend (𝕜 := 𝕜) e := by
  rw [← infinityQuotientExtend_comp_restrict e, ContinuousLinearMap.comp_assoc,
    infinityQuotientRestrict_comp_extend, ContinuousLinearMap.comp_id]

theorem infinityQuotientRestrict_comp_mask (e : ℕ ↪ ℕ) :
    (infinityQuotientRestrict (𝕜 := 𝕜) e).comp (infinityQuotientMask (𝕜 := 𝕜) (Set.range e)) =
      infinityQuotientRestrict (𝕜 := 𝕜) e := by
  rw [← infinityQuotientExtend_comp_restrict e, ← ContinuousLinearMap.comp_assoc,
    infinityQuotientRestrict_comp_extend, ContinuousLinearMap.id_comp]

end ThesisCommon
