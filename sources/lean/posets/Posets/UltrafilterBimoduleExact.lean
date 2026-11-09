import Posets.UltrafilterBimoduleRelations
import Posets.UltrafilterBimoduleExtension

/-! The bimodule argument on arbitrary discrete row and column sets.
Finite fibres ensure that the selector pullbacks act on the full `c₀` spaces;
the common pushforward and almost-everywhere separation are the only
ultrafilter conditions needed by the argument. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Set Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets

abbrev OffDiagonalOn (𝕜 : Type) [RCLike 𝕜] (D R : Type*) :=
  CZeroOn 𝕜 R →L[𝕜] CZeroOn 𝕜 D

namespace ExactUltrafilterBimodule

variable {𝕜 : Type} [RCLike 𝕜] {D R : Type*}

private theorem discrete_tendsto (s : D → R) (hs : ∀ r, (s ⁻¹' {r}).Finite) :
    Tendsto (fun x : Discrete D => (⟨s x.val⟩ : Discrete R))
      (cocompact _) (cocompact _) := by
  rw [cocompact_eq_cofinite, cocompact_eq_cofinite]
  have hv : Function.Injective (Discrete.val : Discrete D → D) := by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl
  have hm : Function.Injective (Discrete.mk : R → Discrete R) := by
    intro x y h
    exact congrArg Discrete.val h
  exact hm.tendsto_cofinite.comp
    ((Filter.Tendsto.cofinite_of_finite_preimage_singleton hs).comp hv.tendsto_cofinite)

private def pullVector (s : D → R) (hs : ∀ r, (s ⁻¹' {r}).Finite)
    (z : CZeroOn 𝕜 R) : CZeroOn 𝕜 D where
  toFun x := z ⟨s x.val⟩
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := (zero_at_infty z).comp (discrete_tendsto s hs)

private theorem pullVector_norm_le (s : D → R) (hs : ∀ r, (s ⁻¹' {r}).Finite)
    (z : CZeroOn 𝕜 R) : ‖pullVector s hs z‖ ≤ ‖z‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg z)).mpr
  intro x
  exact z.toBCF.norm_coe_le_norm ⟨s x.val⟩

private def pull (s : D → R) (hs : ∀ r, (s ⁻¹' {r}).Finite) : OffDiagonalOn 𝕜 D R :=
  ({toFun := pullVector s hs
    map_add' := by intro z w; ext x; rfl
    map_smul' := by intro a z; ext x; rfl} :
      CZeroOn 𝕜 R →ₗ[𝕜] CZeroOn 𝕜 D).mkContinuous 1
    (fun z => by simpa only [one_mul] using pullVector_norm_le s hs z)

private theorem pull_norm_le (s : D → R) (hs : ∀ r, (s ⁻¹' {r}).Finite) :
    ‖pull (𝕜 := 𝕜) s hs‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z => by simpa only [one_mul] using pullVector_norm_le s hs z)

private theorem entry_bound (s : D → R) (T : OffDiagonalOn 𝕜 D R) (x : D) :
    ‖T (unitVector 𝕜 (s x)) ⟨x⟩‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖T (unitVector 𝕜 (s x))‖ := (T (unitVector 𝕜 (s x))).toBCF.norm_coe_le_norm _
    _ ≤ ‖T‖ * ‖unitVector 𝕜 (s x)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left (bimodule_unitVector_norm_le _) (norm_nonneg T)
    _ = ‖T‖ := mul_one _

private def entries (s : D → R) (T : OffDiagonalOn 𝕜 D R) : Discrete D →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => T (unitVector 𝕜 (s x.val)) x) ‖T‖ (fun x => entry_bound s T x.val)

private def entryMap (s : D → R) : OffDiagonalOn 𝕜 D R →L[𝕜] (Discrete D →ᵇ 𝕜) := by
  let E : OffDiagonalOn 𝕜 D R →ₗ[𝕜] (Discrete D →ᵇ 𝕜) :=
    { toFun := entries s
      map_add' := by intro T S; ext x; rfl
      map_smul' := by intro a T; ext x; rfl }
  have hE (T : OffDiagonalOn 𝕜 D R) : ‖E T‖ ≤ 1 * ‖T‖ := by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg T)).mpr
    intro x
    exact entry_bound s T x.val
  exact ⟨E, AddMonoidHomClass.continuous_of_bound E 1 hE⟩

private def read (U : Ultrafilter D) (s : D → R) : OffDiagonalOn 𝕜 D R →L[𝕜] 𝕜 :=
  (ultrafilterEvaluation (𝕜 := 𝕜) U).comp (entryMap (𝕜 := 𝕜) s)

private theorem read_apply (U : Ultrafilter D) (s : D → R) (T : OffDiagonalOn 𝕜 D R) :
    read (𝕜 := 𝕜) U s T = limUnder (U : Filter D) (fun x => T (unitVector 𝕜 (s x)) ⟨x⟩) := rfl

private theorem tendsto_read (U : Ultrafilter D) (s : D → R) (T : OffDiagonalOn 𝕜 D R) :
    Tendsto (fun x => T (unitVector 𝕜 (s x)) ⟨x⟩) (U : Filter D) (𝓝 (read (𝕜 := 𝕜) U s T)) :=
  tendsto_ultrafilter_bounded U _ (entry_bound s T)

private theorem read_left (U : Ultrafilter D) (s : D → R) (a : Discrete D →ᵇ 𝕜)
    (T : OffDiagonalOn 𝕜 D R) :
    read (𝕜 := 𝕜) U s ((multiplicationOperator a).comp T) =
      ultrafilterEvaluation U a * read (𝕜 := 𝕜) U s T := by
  change limUnder (U : Filter D) (fun x => a ⟨x⟩ * T (unitVector 𝕜 (s x)) ⟨x⟩) = _
  exact ((tendsto_ultrafilter_evaluation U a).mul (tendsto_read U s T)).limUnder_eq

private theorem read_right (U : Ultrafilter D) (V : Ultrafilter R) (s : D → R)
    (hs : Ultrafilter.map s U = V) (b : Discrete R →ᵇ 𝕜) (T : OffDiagonalOn 𝕜 D R) :
    read (𝕜 := 𝕜) U s (T.comp (multiplicationOperator b)) =
      read (𝕜 := 𝕜) U s T * ultrafilterEvaluation V b := by
  have ht : Tendsto s (U : Filter D) (V : Filter R) := by
    change Filter.map s (U : Filter D) ≤ (V : Filter R)
    rw [← Ultrafilter.coe_map, hs]
  have hp (x : D) :
      (T.comp (multiplicationOperator b)) (unitVector 𝕜 (s x)) ⟨x⟩ =
        b ⟨s x⟩ * T (unitVector 𝕜 (s x)) ⟨x⟩ := by
    rw [ContinuousLinearMap.comp_apply, multiplicationOperator_unitVector, map_smul]
    rfl
  rw [read_apply]
  simp_rw [hp]
  exact (((tendsto_ultrafilter_evaluation V b).comp ht).mul
    (tendsto_read U s T)).limUnder_eq.trans (mul_comm _ _)

private theorem read_pull (U : Ultrafilter D) (f : ℕ → D → R)
    (hf : ∀ n r, (f n ⁻¹' {r}).Finite)
    (hsep : ∀ n m, n ≠ m → {x | f n x = f m x} ∉ U) (n m : ℕ) :
    read (𝕜 := 𝕜) U (f n) (pull (f m) (hf m)) = if m = n then 1 else 0 := by
  change limUnder (U : Filter D)
    (fun x => (unitVector 𝕜 (f n x)) ⟨f m x⟩) = _
  have hp (x : D) : (unitVector 𝕜 (f n x)) ⟨f m x⟩ =
      if f m x = f n x then (1 : 𝕜) else 0 := by
    by_cases hx : f m x = f n x <;> simp [unitVector, hx]
  simp_rw [hp]
  by_cases hmn : m = n
  · subst m
    simp only
    exact tendsto_const_nhds.limUnder_eq
  · rw [if_neg hmn]
    have hdis : ∀ᶠ x in (U : Filter D), f m x ≠ f n x :=
      Ultrafilter.compl_mem_iff_notMem.mpr (hsep m n hmn)
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [hdis] with x hx
    simp [hx]

end ExactUltrafilterBimodule

open ExactUltrafilterBimodule in
set_option maxHeartbeats 800000 in
/-- Lemma 8.2 for any finite-fibre selector family, on the entire space of
bounded operators from `c₀(R)` to `c₀(D)`. The conclusion uses all bounded
scalar multipliers on the respective discrete index sets. -/
theorem lemma_8_2_of_finite_fibers (𝕜 : Type) [RCLike 𝕜] {D R : Type*}
    (f : ℕ → D → R) (hf : ∀ n r, (f n ⁻¹' {r}).Finite)
    (U : Ultrafilter D) (V : Ultrafilter R)
    (hmap : ∀ n, Ultrafilter.map (f n) U = V)
    (hsep : ∀ n m, n ≠ m → {x | f n x = f m x} ∉ U) :
    ∃ L : OffDiagonalOn 𝕜 D R →ₗ[𝕜] 𝕜, ¬ Continuous L ∧
      (∀ (a : Discrete D →ᵇ 𝕜) (T : OffDiagonalOn 𝕜 D R),
        L ((multiplicationOperator a).comp T) =
          limUnder (U : Filter D) (fun x => a ⟨x⟩) * L T) ∧
      (∀ (b : Discrete R →ᵇ 𝕜) (T : OffDiagonalOn 𝕜 D R),
        L (T.comp (multiplicationOperator b)) =
          L T * limUnder (V : Filter R) (fun x => b ⟨x⟩)) := by
  letI : NormedAddCommGroup (OffDiagonalOn 𝕜 D R) := inferInstance
  letI : NormedSpace 𝕜 (OffDiagonalOn 𝕜 D R) := inferInstance
  let S (n : ℕ) : OffDiagonalOn 𝕜 D R := pull (f n) (hf n)
  let F (n : ℕ) : OffDiagonalOn 𝕜 D R →L[𝕜] 𝕜 := read U (f n)
  obtain ⟨L, hvalues, hzero⟩ := exists_linearMap_of_biorthogonal
    (fun n => (F n).toLinearMap) S
    (by
      intro n m
      by_cases hmn : m = n <;>
        simpa only [hmn, if_true, if_false] using read_pull (𝕜 := 𝕜) U f hf hsep n m)
    (fun n : ℕ => (n : 𝕜))
  refine ⟨L, ?_, ?_, ?_⟩
  · intro hcont
    let Lc : OffDiagonalOn 𝕜 D R →L[𝕜] 𝕜 := ⟨L, hcont⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ‖Lc‖
    have hv : ‖Lc (S n)‖ = (n : ℝ) := by
      change ‖L (S n)‖ = _
      rw [hvalues, RCLike.norm_natCast]
    have hS : ‖S n‖ ≤ 1 := pull_norm_le (f n) (hf n)
    have hb := (Lc.le_opNorm (S n)).trans (mul_le_mul_of_nonneg_left hS (norm_nonneg Lc))
    rw [hv, mul_one] at hb
    exact (not_lt_of_ge hb) hn
  · intro a T
    have hz := hzero ((multiplicationOperator a).comp T - ultrafilterEvaluation U a • T)
      (fun n => by
        change read (𝕜 := 𝕜) U (f n)
          ((multiplicationOperator a).comp T - ultrafilterEvaluation U a • T) = 0
        rw [map_sub, map_smul, read_left, smul_eq_mul, sub_self])
    rw [map_sub, map_smul, smul_eq_mul] at hz
    exact sub_eq_zero.mp hz
  · intro b T
    have hz := hzero (T.comp (multiplicationOperator b) - ultrafilterEvaluation V b • T)
      (fun n => by
        change read (𝕜 := 𝕜) U (f n)
          (T.comp (multiplicationOperator b) - ultrafilterEvaluation V b • T) = 0
        rw [map_sub, map_smul, read_right U V (f n) (hmap n), smul_eq_mul]
        exact sub_eq_zero.mpr (mul_comm _ _))
    rw [map_sub, map_smul, smul_eq_mul] at hz
    exact (sub_eq_zero.mp hz).trans (mul_comm _ _)

end Posets
