import ThesisCommon.Analysis.EllOneColumns
import Mathlib.Analysis.Normed.Module.WeakDual

/-! The canonical scalar ℓ₁–ℓ∞ duality, using the actual absolutely convergent
pairing. This applies to arbitrary coordinate types, in particular subsets of ℕ. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Γ E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

theorem infinityWeakStar_synthesis_summable (v : Γ → E) {C : ℝ}
    (hv : ∀ n, ‖v n‖ ≤ C) (a : lp (fun _ : Γ => 𝕜) 1) :
    Summable (fun n => a n • v n) := by
  apply ((ellOne_hasSum_norm a).summable.mul_right C).of_norm_bounded
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)

def infinityWeakStarSynthesis (v : Γ → E) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) :
    lp (fun _ : Γ => 𝕜) 1 →L[𝕜] E :=
  LinearMap.mkContinuous {
    toFun := fun a => ∑' n, a n • v n
    map_add' := by
      intro a b
      simp only [lp.coeFn_add, Pi.add_apply, add_smul]
      exact (infinityWeakStar_synthesis_summable v hv a).tsum_add
        (infinityWeakStar_synthesis_summable v hv b)
    map_smul' := by
      intro c a
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
      exact tsum_const_smul'' c }
    C (fun a => by
      simpa only [mul_comm C] using
        tsum_of_norm_bounded ((ellOne_hasSum_norm a).mul_right C) (fun n => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)))

theorem norm_infinityWeakStarSynthesis_le (v : Γ → E) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ n, ‖v n‖ ≤ C) : ‖infinityWeakStarSynthesis (𝕜 := 𝕜) v C hv‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem infinityWeakStarSynthesis_single [DecidableEq Γ] (v : Γ → E) (C : ℝ)
    (hv : ∀ n, ‖v n‖ ≤ C) (n : Γ) (c : 𝕜) :
    infinityWeakStarSynthesis v C hv (lp.single 1 n c) = c • v n := by
  change (∑' i, (lp.single 1 n c : lp (fun _ : Γ => 𝕜) 1) i • v i) = _
  rw [tsum_eq_single n]
  · rw [lp.single_apply_self]
  · intro i hi
    simp only [lp.single_apply, Pi.single_eq_of_ne hi, zero_smul]

def infinityWeakStarPair (x : lp (fun _ : Γ => 𝕜) ∞) :
    lp (fun _ : Γ => 𝕜) 1 →L[𝕜] 𝕜 :=
  infinityWeakStarSynthesis x ‖x‖ (lp.norm_apply_le_norm ENNReal.top_ne_zero x)

@[simp] theorem infinityWeakStarPair_apply (x : lp (fun _ : Γ => 𝕜) ∞)
    (a : lp (fun _ : Γ => 𝕜) 1) : infinityWeakStarPair x a = ∑' n, a n * x n := rfl

theorem norm_infinityWeakStarPair_le (x : lp (fun _ : Γ => 𝕜) ∞) :
    ‖infinityWeakStarPair x‖ ≤ ‖x‖ :=
  norm_infinityWeakStarSynthesis_le _ (norm_nonneg _) _

@[simp] theorem infinityWeakStarPair_single [DecidableEq Γ]
    (x : lp (fun _ : Γ => 𝕜) ∞) (n : Γ) (c : 𝕜) :
    infinityWeakStarPair x (lp.single 1 n c) = c * x n :=
  infinityWeakStarSynthesis_single _ _ _ _ _

def infinityWeakStarDualCoordinates [DecidableEq Γ]
    (φ : (lp (fun _ : Γ => 𝕜) 1) →L[𝕜] 𝕜) : lp (fun _ : Γ => 𝕜) ∞ :=
  ⟨fun n => φ (lp.single 1 n (1 : 𝕜)), memℓp_infty ⟨‖φ‖, by
    rintro _ ⟨n, rfl⟩
    simpa only [lp.norm_single (by simp : (0 : ℝ≥0∞) < 1), norm_one, mul_one]
      using φ.le_opNorm (lp.single 1 n (1 : 𝕜))⟩⟩

theorem infinityWeakStarPair_dualCoordinates [DecidableEq Γ]
    (φ : (lp (fun _ : Γ => 𝕜) 1) →L[𝕜] 𝕜) :
    infinityWeakStarPair (infinityWeakStarDualCoordinates φ) = φ := by
  ext a
  have hs := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a).map φ φ.continuous
  rw [infinityWeakStarPair_apply]
  apply HasSum.tsum_eq
  convert hs using 1
  funext n
  change a n * φ (lp.single 1 n (1 : 𝕜)) = φ (lp.single 1 n (a n))
  rw [show (lp.single 1 n (a n) : lp (fun _ : Γ => 𝕜) 1) =
    a n • lp.single 1 n (1 : 𝕜) by rw [← lp.single_smul]; simp]
  exact (map_smul φ _ _).symm

theorem infinityWeakStarDualCoordinates_pair [DecidableEq Γ]
    (x : lp (fun _ : Γ => 𝕜) ∞) :
    infinityWeakStarDualCoordinates (infinityWeakStarPair x) = x := by
  ext n
  change infinityWeakStarPair x (lp.single 1 n (1 : 𝕜)) = x n
  rw [infinityWeakStarPair_single, one_mul]

omit [CompleteSpace E] in
theorem infinityWeakStar_ext_units [DecidableEq Γ]
    (φ ψ : lp (fun _ : Γ => 𝕜) 1 →L[𝕜] E)
    (h : ∀ n, φ (lp.single 1 n (1 : 𝕜)) = ψ (lp.single 1 n (1 : 𝕜))) : φ = ψ := by
  ext a
  have hφ := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a).map φ φ.continuous
  have hψ := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) a).map ψ ψ.continuous
  apply hφ.unique
  convert hψ using 1
  funext n
  simp only [Function.comp_apply]
  rw [show (lp.single 1 n (a n) : lp (fun _ : Γ => 𝕜) 1) =
    a n • lp.single 1 n (1 : 𝕜) by rw [← lp.single_smul]; simp, map_smul, map_smul, h n]

def infinityWeakStarDualIsometry [DecidableEq Γ] :
    lp (fun _ : Γ => 𝕜) ∞ →ₗᵢ[𝕜] (lp (fun _ : Γ => 𝕜) 1 →L[𝕜] 𝕜) where
  toFun := infinityWeakStarPair
  map_add' x y := by
    apply infinityWeakStar_ext_units
    intro n
    simp only [infinityWeakStarPair_single, one_mul, ContinuousLinearMap.add_apply,
      lp.coeFn_add, Pi.add_apply]
  map_smul' c x := by
    apply infinityWeakStar_ext_units
    intro n
    simp only [infinityWeakStarPair_single, one_mul, ContinuousLinearMap.smul_apply,
      lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
  norm_map' x := by
    apply le_antisymm (norm_infinityWeakStarPair_le x)
    apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro n
    have h := (infinityWeakStarPair x).le_opNorm (lp.single 1 n (1 : 𝕜))
    simpa only [infinityWeakStarPair_single, one_mul, lp.norm_single (by simp :
      (0 : ℝ≥0∞) < 1), norm_one, mul_one] using h

/-- The isometric dual identification, including surjectivity onto every
continuous linear functional on ℓ₁. -/
def infinityWeakStarDualEquiv [DecidableEq Γ] :
    lp (fun _ : Γ => 𝕜) ∞ ≃ₗᵢ[𝕜] (lp (fun _ : Γ => 𝕜) 1 →L[𝕜] 𝕜) :=
  LinearIsometryEquiv.ofSurjective infinityWeakStarDualIsometry
    (fun φ => ⟨infinityWeakStarDualCoordinates φ, infinityWeakStarPair_dualCoordinates φ⟩)

/-- The usual weak-star topology transported through the canonical ℓ₁ duality.
Only the topology is changed; points remain the actual bounded sequences. -/
def infinityWeakStarTopology (𝕜 Γ : Type*) [RCLike 𝕜] :
    TopologicalSpace (lp (fun _ : Γ => 𝕜) ∞) :=
  TopologicalSpace.induced
    (fun x => StrongDual.toWeakDual (infinityWeakStarPair x)) inferInstance

theorem infinityWeakStar_continuous_of_preadjoint {Γ : Type*}
    (T : lp (fun _ : Γ => 𝕜) ∞ →L[𝕜] lp (fun _ : Γ => 𝕜) ∞)
    (S : lp (fun _ : Γ => 𝕜) 1 →L[𝕜] lp (fun _ : Γ => 𝕜) 1)
    (h : ∀ x a, infinityWeakStarPair (T x) a = infinityWeakStarPair x (S a)) :
    @Continuous _ _ (infinityWeakStarTopology 𝕜 Γ) (infinityWeakStarTopology 𝕜 Γ) T := by
  letI : TopologicalSpace (lp (fun _ : Γ => 𝕜) ∞) := infinityWeakStarTopology 𝕜 Γ
  apply continuous_induced_rng.mpr
  apply WeakDual.continuous_of_continuous_eval
  intro a
  change Continuous (fun x => infinityWeakStarPair (T x) a)
  simp_rw [h]
  exact (WeakDual.eval_continuous (S a)).comp continuous_induced_dom

end ThesisCommon
