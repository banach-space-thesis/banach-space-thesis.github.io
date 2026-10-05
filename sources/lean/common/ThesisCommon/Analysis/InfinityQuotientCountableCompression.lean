import ThesisCommon.Analysis.InfinityQuotientCompression
import ThesisCommon.Analysis.InfiniteSubsetStabilization

/-! A single genuine quotient mask scalarizes a countable family of
operators. This is the countable selection step in the separable vector
extension of Drewnowski's theorem; no vector operator conclusion is assumed. -/
noncomputable section
namespace ThesisCommon
open Filter
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
variable {𝕜 : Type*} [RCLike 𝕜]

theorem FreeNatUltrafilter.mem_of_finite_diff (U : FreeNatUltrafilter)
    {B C : Set ℕ} (hBC : (B \ C).Finite) (hB : B ∈ U) : C ∈ U := by
  apply Filter.mem_of_superset (Filter.inter_mem hB (U.property hBC.compl_mem_cofinite))
  intro n hn
  by_contra h
  exact hn.2 ⟨hn.1, h⟩

theorem infinityQuotientMask_absorb_of_finite_diff {B C : Set ℕ}
    (hBC : (B \ C).Finite) :
    (infinityQuotientMask (𝕜 := 𝕜) B).comp (infinityQuotientMask (𝕜 := 𝕜) C) =
      infinityQuotientMask (𝕜 := 𝕜) B ∧
    (infinityQuotientMask (𝕜 := 𝕜) C).comp (infinityQuotientMask (𝕜 := 𝕜) B) =
      infinityQuotientMask (𝕜 := 𝕜) B := by
  constructor <;> apply ContinuousLinearMap.ext <;> intro x <;> apply infinityQuotient_ext <;> intro U
  all_goals
    simp only [ContinuousLinearMap.comp_apply, infinityQuotientEval_mask]
    by_cases hB : B ∈ U
    · simp only [if_pos hB, if_pos (U.mem_of_finite_diff hBC hB)]
    · simp only [if_neg hB, ite_self]

theorem infinityQuotient_scalar_compression_mono_mod_finite
    (T : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜)
    {B C : Set ℕ} {c : 𝕜} (hBC : (B \ C).Finite)
    (hT : ∀ x, infinityQuotientMask (𝕜 := 𝕜) C
      (T (infinityQuotientMask (𝕜 := 𝕜) C x)) =
      c • infinityQuotientMask (𝕜 := 𝕜) C x) :
    ∀ x, infinityQuotientMask (𝕜 := 𝕜) B
      (T (infinityQuotientMask (𝕜 := 𝕜) B x)) =
      c • infinityQuotientMask (𝕜 := 𝕜) B x := by
  have h := infinityQuotientMask_absorb_of_finite_diff (𝕜 := 𝕜) hBC
  have hi := infinityQuotientMask_absorb_of_finite_diff (𝕜 := 𝕜)
    (B := B) (C := B) (by simp)
  have hleft (x : InfinityCZeroQuotient 𝕜) :
      infinityQuotientMask (𝕜 := 𝕜) B (infinityQuotientMask (𝕜 := 𝕜) C x) = infinityQuotientMask (𝕜 := 𝕜) B x :=
    congrArg (fun S : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 => S x) h.1
  have hright (x : InfinityCZeroQuotient 𝕜) :
      infinityQuotientMask (𝕜 := 𝕜) C (infinityQuotientMask (𝕜 := 𝕜) B x) = infinityQuotientMask (𝕜 := 𝕜) B x :=
    congrArg (fun S : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 => S x) h.2
  have hid (x : InfinityCZeroQuotient 𝕜) :
      infinityQuotientMask (𝕜 := 𝕜) B (infinityQuotientMask (𝕜 := 𝕜) B x) = infinityQuotientMask (𝕜 := 𝕜) B x :=
    congrArg (fun S : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 => S x) hi.1
  intro x
  have ht := congrArg (infinityQuotientMask (𝕜 := 𝕜) B)
    (hT (infinityQuotientMask (𝕜 := 𝕜) B x))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    hright, hleft, map_smul, hid] using ht

theorem exists_infinityQuotient_countable_scalar_compression
    (T : ℕ → InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ c : ℕ → 𝕜, ∀ n x,
      infinityQuotientMask (𝕜 := 𝕜) B (T n (infinityQuotientMask (𝕜 := 𝕜) B x)) =
        c n • infinityQuotientMask (𝕜 := 𝕜) B x := by
  classical
  let S := {E : Set ℕ // E.Infinite}
  have hstep (n : ℕ) (E : S) := exists_infinityQuotient_scalar_compression (T n) E.property
  choose F hF hFE c hc using hstep
  let states : ℕ → S := fun n => Nat.rec (⟨A, hA⟩ : S)
    (fun n E => ⟨F n E, hF n E⟩) n
  let D : ℕ → Set ℕ := fun n => (states n).val
  have hnest : ∀ n, D (n + 1) ⊆ D n := fun n => hFE n (states n)
  obtain ⟨B, hB, hBA, hfin⟩ := infinite_nested_pseudointersection D
    (fun n => (states n).property) (antitone_nat_of_succ_le hnest)
  refine ⟨B, hB, hBA, fun n => c n (states n), fun n => ?_⟩
  apply infinityQuotient_scalar_compression_mono_mod_finite (T n) (hfin (n + 1))
  intro x
  exact congrArg (fun S : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜 => S x)
    (hc n (states n))

end ThesisCommon

