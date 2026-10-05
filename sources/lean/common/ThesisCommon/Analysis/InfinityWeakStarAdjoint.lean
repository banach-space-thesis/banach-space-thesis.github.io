import ThesisCommon.Analysis.InfinityWeakStarPairing
import ThesisCommon.Analysis.InfinityRestriction
import ThesisCommon.Analysis.LpOperators

/-! The transpose preadjoint on actual ℓ₁(M) for the supported matrix
representation of an ℓ∞ operator. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem infinityWeakStar_restricted_row_bound
    (M : Set ℕ) (v : lp (fun _ : ℕ => 𝕜) 1) :
    ‖lpRestrict (𝕜 := 𝕜) 1 (Function.Embedding.subtype M) v‖ ≤ ‖v‖ := by
  rw [ellOne_norm_eq_tsum, ellOne_norm_eq_tsum]
  exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
    (fun n _ => norm_nonneg (v n)) (fun _ => le_rfl)
    ((ellOne_hasSum_norm v).summable.comp_injective Subtype.val_injective)
    (ellOne_hasSum_norm v).summable

def infinityWeakStarRow
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) (m : ℕ) :
    lp (fun _ : ℕ => 𝕜) 1 :=
  ⟨fun n => T (lp.single ∞ n (1 : 𝕜)) m, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      infinity_functional_row_summable ((lpCoordinate (𝕜 := 𝕜) ∞ m).comp T))⟩

theorem norm_infinityWeakStarRow_le
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) (m : ℕ) :
    ‖infinityWeakStarRow T m‖ ≤ ‖T‖ := by
  rw [ellOne_norm_eq_tsum]
  apply (infinity_functional_row_tsum_le ((lpCoordinate (𝕜 := 𝕜) ∞ m).comp T)).trans
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (norm_lpCoordinate_le ∞ m) (norm_nonneg T)).trans_eq
      (one_mul _))

def infinityWeakStarPreadjoint
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) (M : Set ℕ) :
    lp (fun _ : M => 𝕜) 1 →L[𝕜] lp (fun _ : M => 𝕜) 1 :=
  infinityWeakStarSynthesis
    (fun m : M => lpRestrict (𝕜 := 𝕜) 1 (Function.Embedding.subtype M)
      (infinityWeakStarRow T m)) ‖T‖ (fun m => by
        exact (infinityWeakStar_restricted_row_bound M
          (infinityWeakStarRow T m)).trans (norm_infinityWeakStarRow_le T m))

def infinityWeakStarCompression
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) (M : Set ℕ) :
    lp (fun _ : M => 𝕜) ∞ →L[𝕜] lp (fun _ : M => 𝕜) ∞ :=
  (lpRestrict ∞ (Function.Embedding.subtype M)).comp
    (T.comp (lpExtend ∞ (Function.Embedding.subtype M)))

theorem norm_infinityWeakStarPreadjoint_le
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞) (M : Set ℕ) :
    ‖infinityWeakStarPreadjoint T M‖ ≤ ‖T‖ :=
  norm_infinityWeakStarSynthesis_le _ (norm_nonneg T) _

theorem infinityWeakStarPreadjoint_apply
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    (M : Set ℕ) (a : lp (fun _ : M => 𝕜) 1) (n : M) :
    infinityWeakStarPreadjoint T M a n = ∑' m : M, a m * T (lp.single ∞ n.val (1 : 𝕜)) m.val := by
  let v := fun m : M => lpRestrict (𝕜 := 𝕜) 1 (Function.Embedding.subtype M)
    (infinityWeakStarRow T m)
  have hv : ∀ m, ‖v m‖ ≤ ‖T‖ := fun m =>
    (infinityWeakStar_restricted_row_bound M
      (infinityWeakStarRow T m)).trans (norm_infinityWeakStarRow_le T m)
  have hs := ((infinityWeakStar_synthesis_summable v hv a).hasSum).map
    (lpCoordinate (𝕜 := 𝕜) 1 n) (lpCoordinate (𝕜 := 𝕜) 1 n).continuous
  exact hs.tsum_eq.symm

theorem infinityWeakStarCompression_hasSum
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    {M : Set ℕ}
    (hrep : ∀ m (x : lp (fun _ : ℕ => 𝕜) ∞), (∀ n ∉ M, x n = 0) →
      HasSum (fun n => x n * T (lp.single ∞ n (1 : 𝕜)) m) (T x m))
    (x : lp (fun _ : M => 𝕜) ∞) (m : M) :
    HasSum (fun n : M => x n * T (lp.single ∞ n.val (1 : 𝕜)) m.val)
      (infinityWeakStarCompression T M x m) := by
  let e := Function.Embedding.subtype M
  let y := lpExtend (𝕜 := 𝕜) ∞ e x
  have hy : ∀ n ∉ M, y n = 0 := by
    intro n hn
    change Function.extend e x 0 n = 0
    have he : ¬ ∃ i, e i = n := by
      rintro ⟨i, rfl⟩
      exact hn i.property
    simp only [Function.extend_apply' _ _ _ he, Pi.zero_apply]
  have hs := hrep m y hy
  have hz : ∀ n ∉ Set.range e, y n * T (lp.single ∞ n (1 : 𝕜)) m = 0 := by
    intro n hn
    have hnM : n ∉ M := by
      intro h
      exact hn ⟨⟨n,h⟩, rfl⟩
    rw [hy n hnM, zero_mul]
  have ht := (e.injective.hasSum_iff hz).mpr hs
  change HasSum (fun n : M => y (e n) * T (lp.single ∞ (e n) (1 : 𝕜)) m)
    (T y m) at ht
  simpa only [y, lpExtend_apply_image] using ht

/-- The compression is the genuine Banach adjoint of the transposed matrix
operator. Equality is first checked on ℓ₁ unit vectors and then extended by the
absolutely convergent ℓ₁ expansion. -/
theorem infinityWeakStarCompression_pair
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    {M : Set ℕ}
    (hrep : ∀ m (x : lp (fun _ : ℕ => 𝕜) ∞), (∀ n ∉ M, x n = 0) →
      HasSum (fun n => x n * T (lp.single ∞ n (1 : 𝕜)) m) (T x m))
    (x : lp (fun _ : M => 𝕜) ∞) :
    infinityWeakStarPair (infinityWeakStarCompression T M x) =
      (infinityWeakStarPair x).comp (infinityWeakStarPreadjoint T M) := by
  classical
  apply infinityWeakStar_ext_units
  intro m
  rw [infinityWeakStarPair_single, one_mul, ContinuousLinearMap.comp_apply]
  dsimp only [infinityWeakStarPreadjoint]
  rw [infinityWeakStarSynthesis_single, one_smul, infinityWeakStarPair_apply]
  simpa only [lpRestrict_apply, infinityWeakStarRow, mul_comm] using
    (infinityWeakStarCompression_hasSum T hrep x m).tsum_eq.symm

theorem infinityWeakStarCompression_continuous
    (T : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] lp (fun _ : ℕ => 𝕜) ∞)
    {M : Set ℕ}
    (hrep : ∀ m (x : lp (fun _ : ℕ => 𝕜) ∞), (∀ n ∉ M, x n = 0) →
      HasSum (fun n => x n * T (lp.single ∞ n (1 : 𝕜)) m) (T x m)) :
    @Continuous _ _ (infinityWeakStarTopology 𝕜 M) (infinityWeakStarTopology 𝕜 M)
      (infinityWeakStarCompression T M) := by
  apply infinityWeakStar_continuous_of_preadjoint _ (infinityWeakStarPreadjoint T M)
  intro x a
  exact congrArg (fun φ : lp (fun _ : M => 𝕜) 1 →L[𝕜] 𝕜 => φ a)
    (infinityWeakStarCompression_pair T hrep x)

end ThesisCommon
