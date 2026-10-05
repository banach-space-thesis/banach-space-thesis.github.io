import Posets.OrdinalBandCompression

/-! The selected ambient leaves need not remain dense after taking a section.
First extend fixed-function estimates to their ambient closure, then restrict
along the section. No annulus-mass inequality is asserted at new limit points. -/
noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [TopologicalSpace L] [CompactSpace L]

local instance ordinalBandClosureDualGroup :
    NormedAddCommGroup (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance
local instance ordinalBandClosureDualSpace :
    NormedSpace 𝕜 (JLMS.CZero 𝕜 K →L[𝕜] 𝕜) := inferInstance

theorem ordinalBand_supported_function_error (M : JLMS.AtomicDualModel 𝕜 K)
    (φ : JLMS.CZero 𝕜 K →L[𝕜] 𝕜)
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    (V : Set K) (hVH : V ⊆ H) (g : JLMS.CZero 𝕜 K) (c : 𝕜)
    (hsupp : Function.support g ⊆ H) (hconst : ∀ y ∈ V, g y = c)
    {ε r : ℝ} (hε : 0 ≤ ε) (hgn : ‖g‖ ≤ r) (hcn : ‖c‖ ≤ r)
    (hmass : ‖JLMS.atomicRestriction M (H \ V) φ‖ ≤ ε) :
    ‖φ g - φ (JLMS.clopenIndicator H hH hcH) * c‖ ≤ 2 * ε * r := by
  classical
  let b := JLMS.clopenIndicator (𝕜 := 𝕜) H hH hcH
  let u := g - c • b
  have hu : Function.support u ⊆ H \ V := by
    intro y hy
    have hHy : y ∈ H := by
      by_contra hn
      have hgy : g y = 0 := by by_contra hz; exact hn (hsupp hz)
      exact hy (by simp [u, b, hn, hgy])
    refine ⟨hHy, ?_⟩
    intro hVy
    exact hy (by simp [u, b, hconst y hVy, hVH hVy])
  have hr : 0 ≤ r := (norm_nonneg g).trans hgn
  have hun : ‖u‖ ≤ 2 * r := by
    have hb : ‖c • b‖ ≤ r := by
      rw [norm_smul]
      exact (mul_le_mul hcn (JLMS.norm_clopenIndicator_le H hH hcH)
        (norm_nonneg _) hr).trans_eq (mul_one _)
    exact (norm_sub_le _ _).trans (by linarith)
  have he : φ u = φ g - φ b * c := by simp [u, mul_comm]
  rw [← he, ← ordinalBand_atomic_apply_of_support M φ u hu]
  calc
    _ ≤ ‖JLMS.atomicRestriction M (H \ V) φ‖ * ‖u‖ :=
      (JLMS.atomicRestriction M (H \ V) φ).le_opNorm u
    _ ≤ ε * (2 * r) := mul_le_mul hmass hun (norm_nonneg _) hε
    _ = 2 * ε * r := by ring

theorem ordinalBand_indicator_error (M : JLMS.AtomicDualModel 𝕜 K)
    (φ : JLMS.CZero 𝕜 K →L[𝕜] 𝕜)
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    (V : Set K) (hV : IsClopen V) (hcV : IsCompact V) (hVH : V ⊆ H)
    {ε : ℝ} (hmass : ‖JLMS.atomicRestriction M (H \ V) φ‖ ≤ ε) :
    ‖φ (JLMS.clopenIndicator H hH hcH) - φ (JLMS.clopenIndicator V hV hcV)‖ ≤ ε := by
  classical
  let u := JLMS.clopenIndicator (𝕜 := 𝕜) H hH hcH - JLMS.clopenIndicator V hV hcV
  have hu : Function.support u ⊆ H \ V := by
    intro y hy
    have hHy : y ∈ H := by
      by_contra hn
      have hnV : y ∉ V := fun h => hn (hVH h)
      exact hy (by simp [u, hn, hnV])
    refine ⟨hHy, ?_⟩
    intro hVy
    exact hy (by simp [u, hHy, hVy])
  have hun : ‖u‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
    intro y
    by_cases hVy : y ∈ V
    · simp [u, hVy, hVH hVy]
    · by_cases hHy : y ∈ H <;> simp [u, hVy, hHy]
  rw [← map_sub]
  change ‖φ u‖ ≤ ε
  rw [← ordinalBand_atomic_apply_of_support M φ u hu]
  exact ((JLMS.atomicRestriction M (H \ V) φ).le_opNorm u).trans
    ((mul_le_mul_of_nonneg_left hun (norm_nonneg _)).trans (by simpa using hmass))

theorem ordinalBand_total_lower_from_cell (M : JLMS.AtomicDualModel 𝕜 K)
    (φ : JLMS.CZero 𝕜 K →L[𝕜] 𝕜)
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    (V : Set K) (hV : IsClopen V) (hcV : IsCompact V) (hVH : V ⊆ H)
    {d ε : ℝ} (hd : d ≤ ‖φ (JLMS.clopenIndicator V hV hcV)‖)
    (hmass : ‖JLMS.atomicRestriction M (H \ V) φ‖ ≤ ε) :
    d - ε ≤ ‖φ (JLMS.clopenIndicator H hH hcH)‖ := by
  have he := ordinalBand_indicator_error M φ H hH hcH V hV hcV hVH hmass
  have hn := norm_sub_norm_le (φ (JLMS.clopenIndicator V hV hcV))
    (φ (JLMS.clopenIndicator H hH hcH))
  rw [norm_sub_rev] at hn
  linarith

theorem ordinalBand_factors_from_ambient_closure
    (T : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (J : C(L, 𝕜) →L[𝕜] JLMS.CZero 𝕜 K) (q : C(L, K))
    (H : Set K) (hH : IsClopen H) (hcH : IsCompact H)
    {S : Set K} (hq : ∀ x, q x ∈ closure S)
    (hread : ∀ f : C(L, 𝕜), ∀ x, J f (q x) = f x)
    {d ε : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < d)
    (ha : ∀ y ∈ S, d - ε ≤ ‖T (JLMS.clopenIndicator H hH hcH) y‖)
    (herr : ∀ f : C(L, 𝕜), ∀ y ∈ S,
      ‖T (J f) y - T (JLMS.clopenIndicator H hH hcH) y * J f y‖ ≤ 2 * ε * ‖f‖) :
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] C(L, 𝕜),
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖R‖ ≤ 1 / (d - 3 * ε) := by
  let a := T (JLMS.clopenIndicator (𝕜 := 𝕜) H hH hcH)
  have ha' : ∀ y ∈ closure S, d - ε ≤ ‖a y‖ :=
    closure_minimal ha (isClosed_le continuous_const a.continuous.norm)
  have herr' (f : C(L, 𝕜)) : ∀ y ∈ closure S,
      ‖T (J f) y - a y * J f y‖ ≤ 2 * ε * ‖f‖ :=
    closure_minimal (herr f) (isClosed_le
      ((T (J f)).continuous.sub (a.continuous.mul (J f).continuous)).norm continuous_const)
  apply ordinalBand_factors_of_dense_estimates T J q (ordinalBandTotal T q H hH hcH)
    dense_univ hε hgap
  · intro x _
    exact ha' (q x) (hq x)
  · intro f x _
    simpa only [hread f x] using herr' f (q x) (hq x)

theorem ordinalBand_factors_from_ambient_leaf_mass
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
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜] C(L, 𝕜),
      R.comp (T.comp J) = ContinuousLinearMap.id 𝕜 C(L, 𝕜) ∧ ‖R‖ ≤ 1 / (d - 3 * ε) := by
  apply ordinalBand_factors_from_ambient_closure T J q H hH hcH hq hread hε hgap
  · intro y hy
    exact ordinalBand_total_lower_from_cell M ((JLMS.evaluation y).comp T)
      H hH hcH (V y) (hV y hy) (hcV y hy) (hVH y hy) (hd y hy) (hmass y hy)
  · intro f y hy
    have hJn : ‖J f‖ ≤ ‖f‖ := (J.le_opNorm f).trans (by
      simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg f))
    exact ordinalBand_supported_function_error M ((JLMS.evaluation y).comp T)
      H hH hcH (V y) (hVH y hy) (J f) (J f y) (hsupp f) (hconst y hy f)
      hε hJn ((JLMS.norm_CZero_apply_le (J f) y).trans hJn) (hmass y hy)

end Posets
