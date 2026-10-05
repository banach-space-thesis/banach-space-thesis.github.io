import ThesisCommon.Analysis.MilutinBinaryRetraction

/-! Milutin's regular averaging lemma for the actual binary Cantor space.
The proof keeps Ditor's finite-cover and inverse-limit averaging construction.
The final topological step uses an explicit closed binary encoding and a
continuous retraction, rather than requiring the general Cantor-space
homeomorphism classification theorem. -/

noncomputable section
open Set
namespace ThesisCommon

theorem milutin_binary_cantor_regular_averaging {𝕜 : Type*} [RCLike 𝕜]
    (K : Type*) [MetricSpace K] [CompactSpace K] [Nonempty K] :
    ∃ q : C((ℕ → Bool), K), Function.Surjective q ∧
      ∃ A : C((ℕ → Bool), 𝕜) →L[𝕜] C(K, 𝕜),
        ‖A‖ = 1 ∧ A.comp (continuousMapPullback q) = ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
  let B := MilutinCompactMetric.of K
  let L := MilutinCompactLimit B
  let i : C(L, ℕ → Bool) := milutinCompactBinaryCode B
  let P : C(L, K) := milutinCompactProjection B
  have hi := milutinCompactBinaryCode_isClosedEmbedding B
  have hP := milutinCompactProjection_surjective B
  have hnonempty : (Set.range i).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty K›
    obtain ⟨z, _⟩ := hP x
    exact ⟨i z, z, rfl⟩
  let e : L ≃ₜ Set.range i := hi.isEmbedding.toHomeomorph
  let r : C((ℕ → Bool), L) :=
    (⟨e.symm, e.symm.continuous⟩ : C(Set.range i, L)).comp
      (milutinBinaryRetraction (Set.range i) hnonempty hi.isClosed_range)
  have hri (z : L) : r (i z) = z := by
    change e.symm (milutinBinaryRetraction (Set.range i) hnonempty hi.isClosed_range (e z).val) = z
    rw [milutinBinaryRetraction_apply_subtype, e.symm_apply_apply]
  let q : C((ℕ → Bool), K) := P.comp r
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨z, hz⟩ := hP x
    exact ⟨i z, by change P (r (i z)) = x; rw [hri]; exact hz⟩
  obtain ⟨A₀, hA₀, hA₀P⟩ := milutinCompactProjection_regular_averaging (𝕜 := 𝕜) B
  let A : C((ℕ → Bool), 𝕜) →L[𝕜] C(K, 𝕜) := A₀.comp (continuousMapPullback i)
  have hA : ‖A‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [hA₀, one_mul]
    exact norm_continuousMapPullback_le i
  have hAJ : A.comp (continuousMapPullback q) = ContinuousLinearMap.id 𝕜 C(K, 𝕜) := by
    apply ContinuousLinearMap.ext
    intro f
    have hcomp : continuousMapPullback i (continuousMapPullback q f) = continuousMapPullback P f := by
      ext z
      change f (P (r (i z))) = f (P z)
      rw [hri]
    change A₀ (continuousMapPullback i (continuousMapPullback q f)) = f
    rw [hcomp]
    exact congrArg (fun T : C(K, 𝕜) →L[𝕜] C(K, 𝕜) => T f) hA₀P
  refine ⟨q, hq, A, le_antisymm hA ?_, hAJ⟩
  have h := ContinuousLinearMap.opNorm_comp_le A (continuousMapPullback q)
  rw [hAJ, ContinuousLinearMap.norm_id] at h
  apply h.trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (norm_continuousMapPullback_le (𝕜 := 𝕜) q) (norm_nonneg A)

end ThesisCommon
