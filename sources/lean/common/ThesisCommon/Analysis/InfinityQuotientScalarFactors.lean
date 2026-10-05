import ThesisCommon.Analysis.InfinityQuotientReindex
import ThesisCommon.Analysis.ScalarCompressionFactors

/-! Turning an actual scalar band compression of ℓ∞/c₀ into the exact
2-factorization dichotomy using genuine quotient reindex contractions. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinityQuotient_mask_retracts (e : ℕ ↪ ℕ) {B : Set ℕ}
    (heB : Set.range e ⊆ B) :
    (infinityQuotientMask (𝕜 := 𝕜) B).comp (infinityQuotientExtend (𝕜 := 𝕜) e) =
        infinityQuotientExtend (𝕜 := 𝕜) e ∧
      (infinityQuotientRestrict (𝕜 := 𝕜) e).comp (infinityQuotientMask (𝕜 := 𝕜) B) =
        infinityQuotientRestrict (𝕜 := 𝕜) e := by
  let P := infinityQuotientMask (𝕜 := 𝕜) B
  let P' := infinityQuotientMask (𝕜 := 𝕜) (Set.range e)
  let R := infinityQuotientRestrict (𝕜 := 𝕜) e
  let V := infinityQuotientExtend (𝕜 := 𝕜) e
  have hPP' : P.comp P' = P' := by
    dsimp [P, P']
    rw [infinityQuotientMask_comp, Set.inter_eq_right.mpr heB]
  have hP'P : P'.comp P = P' := by
    dsimp [P, P']
    rw [infinityQuotientMask_comp, Set.inter_eq_left.mpr heB]
  have hP'V : P'.comp V = V := infinityQuotientMask_comp_extend e
  have hRP' : R.comp P' = R := infinityQuotientRestrict_comp_mask e
  constructor
  · change P.comp V = V
    calc
      P.comp V = P.comp (P'.comp V) := congrArg P.comp hP'V.symm
      _ = (P.comp P').comp V := (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = V := by rw [hPP', hP'V]
  · change R.comp P = R
    calc
      R.comp P = (R.comp P').comp P := congrArg (fun S => S.comp P) hRP'.symm
      _ = R.comp (P'.comp P) := ContinuousLinearMap.comp_assoc _ _ _
      _ = R := by rw [hP'P, hRP']

theorem infinityQuotient_factor_dichotomy_of_mask_compression
    (T : InfinityCZeroQuotient 𝕜 →L[𝕜] InfinityCZeroQuotient 𝕜)
    (B : Set ℕ) (c : 𝕜) (hB : B.Infinite)
    (hcomp : ((infinityQuotientMask (𝕜 := 𝕜) B).comp T).comp
      (infinityQuotientMask (𝕜 := 𝕜) B) = c • infinityQuotientMask (𝕜 := 𝕜) B) :
    FactorsIdentityWith T (InfinityCZeroQuotient 𝕜) 2 ∨
      FactorsIdentityWith (ContinuousLinearMap.id 𝕜 (InfinityCZeroQuotient 𝕜) - T)
        (InfinityCZeroQuotient 𝕜) 2 := by
  let e : ℕ ↪ ℕ := (hB.natEmbedding B).trans (Function.Embedding.subtype B)
  have heB : Set.range e ⊆ B := by
    rintro n ⟨k, rfl⟩
    exact (hB.natEmbedding B k).property
  let R := infinityQuotientRestrict (𝕜 := 𝕜) e
  let V := infinityQuotientExtend (𝕜 := 𝕜) e
  obtain ⟨hPV, hRP⟩ := infinityQuotient_mask_retracts (𝕜 := 𝕜) e heB
  have hRV : R.comp V = ContinuousLinearMap.id 𝕜 (InfinityCZeroQuotient 𝕜) :=
    infinityQuotientRestrict_comp_extend e
  apply scalar_compression_factor_dichotomy T R V c
    (norm_infinityQuotientRestrict_le e) (norm_infinityQuotientExtend_le e) hRV
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg R (DFunLike.congr_fun hcomp (V x))
  have hpv : infinityQuotientMask (𝕜 := 𝕜) B (V x) = V x := DFunLike.congr_fun hPV x
  have hrp (y) : R (infinityQuotientMask (𝕜 := 𝕜) B y) = R y := DFunLike.congr_fun hRP y
  have hrv : R (V x) = x := DFunLike.congr_fun hRV x
  change R (infinityQuotientMask (𝕜 := 𝕜) B
    (T (infinityQuotientMask (𝕜 := 𝕜) B (V x)))) =
      R (c • infinityQuotientMask (𝕜 := 𝕜) B (V x)) at h
  rw [hpv, hrp, map_smul, hrv] at h
  exact h

end ThesisCommon
