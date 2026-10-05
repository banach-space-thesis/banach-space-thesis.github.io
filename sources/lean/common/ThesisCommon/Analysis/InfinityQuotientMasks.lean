import ThesisCommon.Analysis.InfinityQuotientEvaluation
import ThesisCommon.Analysis.InfinityMask

/-! Genuine coordinate masks and indicator classes in ℓ∞/c₀. Their
ultrafilter formulas express localization modulo finite sets. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace ThesisCommon
attribute [local instance] Classical.propDecidable
variable {𝕜 : Type*} [RCLike 𝕜]

def scalarBoundedConstant (c : 𝕜) : lp (fun _ : ℕ => 𝕜) ∞ :=
  ⟨fun _ => c, memℓp_infty ⟨‖c‖, by rintro _ ⟨n, rfl⟩; exact le_rfl⟩⟩

theorem infinityMask_mem_cZero (A : Set ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞)
    (hx : x ∈ scalarCZeroSubmodule 𝕜) : infinityMask A x ∈ scalarCZeroSubmodule 𝕜 := by
  apply squeeze_zero_norm (a := fun n => ‖x n‖)
  · intro n
    by_cases hn : n ∈ A <;> simp [hn]
  · simpa only [norm_zero] using hx.norm

def infinityQuotientMask (A : Set ℕ) : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 :=
  quotientMapL (scalarCZeroSubmodule 𝕜) (scalarCZeroSubmodule 𝕜)
    (infinityMask A) (infinityMask_mem_cZero A)

@[simp] theorem infinityQuotientMask_mk (A : Set ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞) :
    infinityQuotientMask (𝕜 := 𝕜) A (infinityQuotientMk (𝕜 := 𝕜) x) = infinityQuotientMk (𝕜 := 𝕜) (infinityMask A x) := rfl

theorem norm_infinityQuotientMask_le (A : Set ℕ) :
    ‖infinityQuotientMask (𝕜 := 𝕜) A‖ ≤ 1 := by
  apply (norm_quotientMapL_le _ _ _ _).trans
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa only [one_mul] using norm_infinityMask_apply_le A x)

@[simp] theorem infinityQuotientEval_mask (U : FreeNatUltrafilter) (A : Set ℕ)
    (x : InfinityCZeroQuotient 𝕜) :
    infinityQuotientEval (𝕜 := 𝕜) U (infinityQuotientMask (𝕜 := 𝕜) A x) =
      if A ∈ U then infinityQuotientEval (𝕜 := 𝕜) U x else 0 := by
  induction x using Quotient.inductionOn' with
  | h x =>
    change scalarUltralimit U.val (infinityMask A x) = if A ∈ U then scalarUltralimit U.val x else 0
    by_cases hA : A ∈ U
    · rw [if_pos hA]
      apply scalarUltralimit_eq_of_tendsto
      apply (scalarUltralimit_tendsto U.val x).congr'
      filter_upwards [hA] with n hn
      simp [hn]
    · rw [if_neg hA]
      apply scalarUltralimit_eq_of_tendsto
      apply tendsto_const_nhds.congr'
      have hc : Aᶜ ∈ (U.val : Filter ℕ) := U.val.compl_mem_iff_notMem.mpr hA
      filter_upwards [hc] with n hn
      simp [show n ∉ A from hn]

def infinityQuotientIndicator (A : Set ℕ) : InfinityCZeroQuotient 𝕜 :=
  infinityQuotientMk (𝕜 := 𝕜) (infinityMask A (scalarBoundedConstant 1))

@[simp] theorem infinityQuotientEval_indicator (U : FreeNatUltrafilter) (A : Set ℕ) :
    infinityQuotientEval (𝕜 := 𝕜) U (infinityQuotientIndicator (𝕜 := 𝕜) A) = if A ∈ U then 1 else 0 := by
  change infinityQuotientEval (𝕜 := 𝕜) U (infinityQuotientMask (𝕜 := 𝕜) A
    (infinityQuotientMk (𝕜 := 𝕜) (scalarBoundedConstant (1 : 𝕜)))) = _
  rw [infinityQuotientEval_mask, infinityQuotientEval_mk]
  rw [scalarUltralimit_eq_of_tendsto U.val _ (z := (1 : 𝕜)) tendsto_const_nhds]

theorem norm_infinityQuotientIndicator_le (A : Set ℕ) :
    ‖infinityQuotientIndicator (𝕜 := 𝕜) A‖ ≤ 1 := by
  apply (Submodule.Quotient.norm_mk_le _ _).trans
  apply (norm_infinityMask_apply_le _ _).trans
  apply lp.norm_le_of_forall_le zero_le_one
  intro n
  exact norm_one.le

theorem infinityQuotientMask_comp (A B : Set ℕ) :
    (infinityQuotientMask (𝕜 := 𝕜) A).comp (infinityQuotientMask (𝕜 := 𝕜) B) =
      infinityQuotientMask (𝕜 := 𝕜) (A ∩ B) := by
  apply ContinuousLinearMap.ext
  intro x
  apply infinityQuotient_ext
  intro U
  simp only [ContinuousLinearMap.comp_apply, infinityQuotientEval_mask]
  have h : A ∩ B ∈ U ↔ A ∈ U ∧ B ∈ U := Filter.inter_mem_iff
  rw [h]
  split_ifs <;> aesop

theorem infinityQuotientIndicator_empty : infinityQuotientIndicator (𝕜 := 𝕜) ∅ = 0 := by
  apply infinityQuotient_ext
  intro U
  simp only [infinityQuotientEval_indicator, map_zero]
  exact if_neg (Filter.empty_notMem (f := (U.val : Filter ℕ)))

theorem infinityQuotientIndicator_union {A B : Set ℕ} (hAB : Disjoint A B) :
    infinityQuotientIndicator (𝕜 := 𝕜) (A ∪ B) =
      infinityQuotientIndicator (𝕜 := 𝕜) A + infinityQuotientIndicator (𝕜 := 𝕜) B := by
  change infinityQuotientMk (𝕜 := 𝕜) _ = infinityQuotientMk (𝕜 := 𝕜) _ + infinityQuotientMk (𝕜 := 𝕜) _
  rw [← map_add]
  congr 1
  apply lp.ext
  funext n
  simp only [infinityMask_apply, lp.coeFn_add, Pi.add_apply]
  change (if n ∈ A ∪ B then (1 : 𝕜) else 0) =
    (if n ∈ A then 1 else 0) + (if n ∈ B then 1 else 0)
  have hd := Set.disjoint_left.mp hAB
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp_all

theorem infinityQuotientIndicator_sdiff {A B : Set ℕ} (hBA : B ⊆ A) :
    infinityQuotientIndicator (𝕜 := 𝕜) (A \ B) =
      infinityQuotientIndicator (𝕜 := 𝕜) A - infinityQuotientIndicator (𝕜 := 𝕜) B := by
  have h := infinityQuotientIndicator_union (𝕜 := 𝕜) (A := A \ B) (B := B) Set.disjoint_sdiff_left
  have heq : A \ B ∪ B = A := by
    ext n
    constructor
    · rintro (⟨hn, _⟩ | hn)
      · exact hn
      · exact hBA hn
    · intro hn
      by_cases hb : n ∈ B
      · exact Or.inr hb
      · exact Or.inl ⟨hn, hb⟩
  rw [heq] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem infinityQuotientIndicator_remove_finite (A K : Set ℕ) (hK : K.Finite) :
    infinityQuotientIndicator (𝕜 := 𝕜) (A \ K) = infinityQuotientIndicator (𝕜 := 𝕜) A := by
  apply infinityQuotient_ext
  intro U
  simp only [infinityQuotientEval_indicator]
  have hmem : A \ K ∈ U ↔ A ∈ U := by
    constructor
    · intro h
      exact Filter.mem_of_superset h Set.diff_subset
    · intro h
      exact Filter.inter_mem h (U.property hK.compl_mem_cofinite)
  rw [hmem]

end ThesisCommon

