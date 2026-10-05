import Posets.OrdinalBandCompressionClosure

/-! The local inverse is kept on the coordinate function space. This exposes
the form needed for a uniformly bounded family of inverses on a genuine c₀
sum, instead of retaining only an existential ambient factorization. -/
noncomputable section
namespace Posets
open Set Topology
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

theorem ordinalBand_coordinate_inverse_from_closure
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K))
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    {S : Set K} (hq : ∀ x, q x ∈ closure S)
    (hread : ∀ f : C(L, 𝕜), ∀ x, J f (q x) = f x)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (ha : ∀ y ∈ S, d - ε ≤ ‖T (JLMS.clopenIndicator H hH hcH) y‖)
    (herr : ∀ f : C(L, 𝕜), ∀ y ∈ S,
      ‖T (J f) y - T (JLMS.clopenIndicator H hH hcH) y * J f y‖ ≤ 2 * ε * ‖f‖) :
    ∃ B : C(L, 𝕜) →L[𝕜] C(L, 𝕜),
      B.comp (ordinalBandCompression T J q) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧
        ‖B‖ ≤ 1 / (d - 3 * ε) := by
  let a := T (JLMS.clopenIndicator (𝕜 := 𝕜) H hH hcH)
  have ha' : ∀ y ∈ closure S, d - ε ≤ ‖a y‖ :=
    closure_minimal ha (isClosed_le continuous_const a.continuous.norm)
  have he' (f : C(L, 𝕜)) : ∀ y ∈ closure S,
      ‖T (J f) y - a y * J f y‖ ≤ 2 * ε * ‖f‖ :=
    closure_minimal (herr f) (isClosed_le
      ((T (J f)).continuous.sub (a.continuous.mul (J f).continuous)).norm continuous_const)
  apply ordinalBand_inverse_of_multiplier_error (ordinalBandCompression T J q)
    (ordinalBandTotal T q H hH hcH) hε hgap
  · intro x
    exact ha' (q x) (hq x)
  · apply ordinalBand_error_of_dense_leaves _ _ dense_univ (mul_nonneg (by norm_num) hε)
    intro f x _
    simpa only [hread f x] using he' f (q x) (hq x)

theorem ordinalBand_coordinate_inverse_from_leaf_mass
    (M : JLMS.AtomicDualModel 𝕜 K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K))
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    (hJ : ‖J‖ ≤ 1) (hsupp : ∀ f, Function.support (J f) ⊆ H)
    {S : Set K} (hq : ∀ x, q x ∈ closure S)
    (hread : ∀ f : C(L, 𝕜), ∀ x, J f (q x) = f x)
    (V : K → Set K) (hVH : ∀ y ∈ S, V y ⊆ H)
    (hV : ∀ y ∈ S, IsClopen (V y)) (hcV : ∀ y ∈ S, IsCompact (V y))
    (hconst : ∀ y ∈ S, ∀ f : C(L, 𝕜), ∀ z ∈ V y, J f z = J f y)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (hd : ∀ y (hy : y ∈ S), d ≤ ‖T (JLMS.clopenIndicator (V y) (hV y hy) (hcV y hy)) y‖)
    (hmass : ∀ y ∈ S, ‖JLMS.atomicRestriction M (H \ V y)
      ((JLMS.evaluation y).comp T)‖ ≤ ε) :
    ∃ B : C(L, 𝕜) →L[𝕜] C(L, 𝕜),
      B.comp (ordinalBandCompression T J q) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧
        ‖B‖ ≤ 1 / (d - 3 * ε) := by
  apply ordinalBand_coordinate_inverse_from_closure T J q H hH hcH hq hread hε hgap
  · intro y hy
    exact ordinalBand_total_lower_from_cell M ((JLMS.evaluation y).comp T)
      H hH hcH (V y) (hV y hy) (hcV y hy) (hVH y hy) (hd y hy) (hmass y hy)
  · intro f y hy
    have hJn : ‖J f‖ ≤ ‖f‖ := (J.le_opNorm f).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ (norm_nonneg f))
    exact ordinalBand_supported_function_error M ((JLMS.evaluation y).comp T)
      H hH hcH (V y) (hVH y hy) (J f) (J f y) (hsupp f) (hconst y hy f)
      hε hJn ((JLMS.norm_CZero_apply_le (J f) y).trans hJn) (hmass y hy)

end Posets
