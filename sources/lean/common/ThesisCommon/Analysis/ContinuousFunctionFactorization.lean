import ThesisCommon.Analysis.ContinuousClopenCopies
import ThesisCommon.Analysis.Factorization

/-! Factorizations lift to continuous-function spaces with the same product
bound. Contractive clopen insertion/readback then transfers a genuine local
coefficient factorization to the original operator. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 K X Y Z : Type*} [RCLike 𝕜] [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def continuousFunctionPostcompose (u : X →L[𝕜] Y) : C(K, X) →L[𝕜] C(K, Y) :=
  ContinuousLinearMap.compLeftContinuous 𝕜 K u

omit [CompactSpace K] in
@[simp] theorem continuousFunctionPostcompose_apply (u : X →L[𝕜] Y)
    (f : C(K, X)) (U : K) : continuousFunctionPostcompose u f U = u (f U) := rfl

theorem norm_continuousFunctionPostcompose_le (u : X →L[𝕜] Y) :
    ‖continuousFunctionPostcompose (K := K) u‖ ≤ ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u)
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg u) (norm_nonneg f))).mpr
  intro U
  exact (u.le_opNorm (f U)).trans
    (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm U) (norm_nonneg u))

theorem FactorsIdentityWith.continuousFunctions {T : X →L[𝕜] Y} {C : ℝ}
    (h : FactorsIdentityWith T Z C) :
    FactorsIdentityWith (continuousFunctionPostcompose (K := K) T) C(K, Z) C := by
  obtain ⟨U, V, he, hn⟩ := h
  refine ⟨continuousFunctionPostcompose U, continuousFunctionPostcompose V, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    ext k
    exact congrArg (fun S : Z →L[𝕜] Z => S (f k)) he
  · exact (mul_le_mul (norm_continuousFunctionPostcompose_le U)
      (norm_continuousFunctionPostcompose_le V) (norm_nonneg _)
      (norm_nonneg U)).trans hn

theorem FactorsIdentityWith.of_clopen_coefficient
    (T : C(K, X) →L[𝕜] C(K, X)) (A : Set K) (hA : IsClopen A) (e : K ≃ₜ A)
    (u : X →L[𝕜] X)
    (hTu : ∀ f : C(K, X), (∀ k, k ∉ A → f k = 0) →
      ∀ k ∈ A, T f k = u (f k)) {C : ℝ} (hu : FactorsIdentityWith u X C) :
    FactorsIdentityWith T C(K, X) C := by
  let J := continuousClopenInsert (𝕜 := 𝕜) (X := X) A hA e
  let R := continuousClopenRead (𝕜 := 𝕜) (X := X) A e
  have hcomp : (R.comp T).comp J = continuousFunctionPostcompose (K := K) u := by
    apply ContinuousLinearMap.ext
    intro f
    ext k
    change T (J f) (e k).val = u (f k)
    rw [hTu (J f) (by
      intro k hk
      simp only [J, continuousClopenInsert_apply, dif_neg hk]) (e k).val (e k).property]
    congr 1
    change continuousClopenInsert (𝕜 := 𝕜) A hA e f (e k).val = f k
    rw [continuousClopenInsert_apply, dif_pos (e k).property]
    exact congrArg f (e.symm_apply_apply k)
  have h := hu.continuousFunctions (K := K)
  rw [← hcomp] at h
  apply (h.of_compression R J).mono
  have hC : 0 ≤ C := by
    obtain ⟨U, V, _, hn⟩ := hu
    exact (mul_nonneg (norm_nonneg U) (norm_nonneg V)).trans hn
  have hRJ : ‖R‖ * ‖J‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul
      (norm_continuousClopenRead_le (𝕜 := 𝕜) (X := X) A e)
      (norm_continuousClopenInsert_le (𝕜 := 𝕜) (X := X) A hA e)
      (norm_nonneg J) zero_le_one
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hRJ hC

theorem FactorsIdentity.of_clopen_coefficient
    (T : C(K, X) →L[𝕜] C(K, X)) (A : Set K) (hA : IsClopen A) (e : K ≃ₜ A)
    (u : X →L[𝕜] X)
    (hTu : ∀ f : C(K, X), (∀ k, k ∉ A → f k = 0) →
      ∀ k ∈ A, T f k = u (f k)) (hu : FactorsIdentity u X) :
    FactorsIdentity T C(K, X) := by
  obtain ⟨C, _, hC⟩ := (factorsIdentity_iff_exists_bound u).mp hu
  exact (hC.of_clopen_coefficient T A hA e u hTu).forget_bound

end ThesisCommon
