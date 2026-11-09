import ThesisCommon.Analysis.OrdinalInfinitySelection
import ThesisCommon.Analysis.IntervalSmallBlocks

/-! The ordinal alternative of LPCK Lemma 5.1, with the actual closed
sets and restriction maps in the conclusion. -/
noncomputable section
open scoped ENNReal
namespace LPCK.Printed
open ThesisCommon

universe u
variable {𝕜 : Type*} [RCLike 𝕜]

private theorem norm_restrict_range_le {K X : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (g : C(K, K)) [CompactSpace (Set.range g)] (R : C(K, 𝕜) →L[𝕜] C(K, 𝕜))
    (hR : ∀ f t, R f t = f (g t))
    (S : X →L[𝕜] C(K, 𝕜)) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ‖R.comp S‖ ≤ ε) :
    ‖(continuousMapRestrict (Set.range g)).comp S‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε
  intro x hx
  apply (ContinuousMap.norm_le _ hε).mpr
  rintro ⟨y, t, rfl⟩
  change ‖S x (g t)‖ ≤ ε
  rw [← hR]
  exact ((R (S x)).norm_coe_le_norm t).trans
    (((R.comp S).le_opNorm x).trans (by simpa only [hx, mul_one] using h))

/-- LPCK Lemma 5.1, characteristic-one ordinal interval case. -/
theorem lemma_5_1_ordinal {α η a : Ordinal.{u}}
    (hD : ordinalDerived (Set.Icc 0 α) η = {a})
    (T : EllInfinitySum (OrdinalContinuous 𝕜 α) →L[𝕜]
      EllInfinitySum (OrdinalContinuous 𝕜 α)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (e : ℕ ↪ ℕ) (A : ℕ → Set (OrdinalInterval α)),
      ∀ k, ∃ hA : IsClosed (A k), Nonempty (OrdinalInterval α ≃ₜ A k) ∧
        (letI : CompactSpace (A k) := isCompact_iff_compactSpace.mp hA.isCompact
         ‖(continuousMapRestrict (A k)).comp (lpEntry T (e k) n)‖ ≤ ε) := by
  obtain ⟨f, c, hf, hsmall⟩ := ordinal_infinity_upper_selection hD T (fun _ => ε) (fun _ => hε)
  let e : ℕ ↪ ℕ := ⟨fun k => f (k + 1), fun i j h => Nat.succ.inj (f.injective h)⟩
  refine ⟨f 0, e, fun k => Set.range (ordinalChainMap (c (k + 1))), ?_⟩
  intro k
  obtain ⟨hA, he⟩ := ordinalChainMap_closed_copy (c (k + 1))
  refine ⟨hA, he, ?_⟩
  letI : CompactSpace (Set.range (ordinalChainMap (c (k + 1)))) :=
    isCompact_iff_compactSpace.mp hA.isCompact
  apply norm_restrict_range_le (ordinalChainMap (c (k + 1))) (ordinalChainRead (c (k + 1)))
    (ordinalChainRead_apply _) _ hε.le
  simpa only [e, lpEntry, ContinuousLinearMap.comp_assoc] using hsmall 0 (k + 1) (Nat.zero_lt_succ k)

end LPCK.Printed
