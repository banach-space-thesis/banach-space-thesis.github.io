import Posets.OrdinalCofinalBlockModel

/-! A genuine embedding of a limit ordinal function space in a c₀ sum of
countable compact spaces with cofinal Cantor–Bendixson ranks.  Its distortion
comes only from the fixed ordinal block model, not from the target spaces.
-/
noncomputable section
open Set Order ThesisCommon
open scoped Ordinal
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

local instance ordinalCofinalEmbeddingFunctionGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (OrdinalContinuous 𝕜 α) := inferInstance
local instance ordinalCofinalEmbeddingFunctionSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (OrdinalContinuous 𝕜 α) := inferInstance
local instance ordinalCofinalEmbeddingEndpointGroup (α : Ordinal.{0}) :
    NormedAddCommGroup (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance ordinalCofinalEmbeddingEndpointSpace (α : Ordinal.{0}) :
    NormedSpace 𝕜 (JLMS.ordinalEndpointZero 𝕜 α) := inferInstance
local instance ordinalCofinalEmbeddingSumGroup {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedAddCommGroup (JLMS.CZeroSum 𝕜 E) := inferInstance
local instance ordinalCofinalEmbeddingSumSpace {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    NormedSpace 𝕜 (JLMS.CZeroSum 𝕜 E) := inferInstance

theorem exists_ordinalCofinalBlockEmbedding
    (γ : Ordinal.{0}) (hγ : IsSuccLimit γ) (hc : γ.card ≤ Cardinal.aleph0)
    (Q : ℕ → Type*) [∀ n, TopologicalSpace (Q n)] [∀ n, CompactSpace (Q n)]
    [∀ n, T2Space (Q n)] [∀ n, Countable (Q n)]
    (β : ℕ → Ordinal.{0}) (hβ : Monotone β)
    (hcof : ∀ α < γ, ∃ n, α ≤ β n)
    (hD : ∀ n, (ordinalDerived (univ : Set (Q n)) (β n)).Nonempty) :
    ∃ J : OrdinalContinuous 𝕜 (ω ^ γ) →L[𝕜] JLMS.CZeroSum 𝕜 (fun n => C(Q n, 𝕜)),
      ‖J‖ ≤ ‖(ordinalCofinalBlockEquiv (𝕜 := 𝕜) γ hγ hc).toContinuousLinearMap‖ ∧
      ∀ f, ‖f‖ ≤ ‖(ordinalCofinalBlockEquiv (𝕜 := 𝕜) γ hγ hc).symm.toContinuousLinearMap‖ * ‖J f‖ := by
  classical
  let δ := ordinalCofinalBlockExponent γ hγ hc
  obtain ⟨k, hk, hkβ⟩ := exists_strictMono_cofinal_block_selection β δ hβ hcof
    (ordinalCofinalBlockExponent_lt γ hγ hc)
  have hcopies (n : ℕ) : Nonempty (OrdinalContinuous 𝕜 (ω ^ δ n) →ₗᵢ[𝕜] C(Q (k n), 𝕜)) := by
    apply exists_ordinal_isometry_of_derivative_nonempty (Q (k n))
      (ordinalCofinalBlockExponent_ne_zero γ hγ hc n)
    exact (hD (k n)).mono (ordinalDerived_antitone isClosed_univ (hkβ n))
  let V (n : ℕ) : OrdinalContinuous 𝕜 (ω ^ δ n) →ₗᵢ[𝕜] C(Q (k n), 𝕜) := (hcopies n).some
  let W (n : ℕ) : JLMS.ordinalEndpointZero 𝕜 (ω ^ δ n) →ₗᵢ[𝕜] C(Q (k n), 𝕜) :=
    (V n).comp (JLMS.ordinalEndpointZero 𝕜 (ω ^ δ n)).subtypeₗᵢ
  let S := (cZeroSum_insertIsometry (𝕜 := 𝕜) (E := fun n => C(Q n, 𝕜)) k hk.injective).comp
    (cZeroSum_mapIsometry (𝕜 := 𝕜)
      (E := fun n => ↥(JLMS.ordinalEndpointZero 𝕜 (ω ^ δ n)))
      (F := fun n => C(Q (k n), 𝕜)) W)
  let e := ordinalCofinalBlockEquiv (𝕜 := 𝕜) γ hγ hc
  let J := S.toContinuousLinearMap.comp e.toContinuousLinearMap
  have hnorm (f : OrdinalContinuous 𝕜 (ω ^ γ)) : ‖J f‖ = ‖e f‖ := S.norm_map (e f)
  refine ⟨J, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    rw [hnorm]
    exact e.toContinuousLinearMap.le_opNorm f
  · intro f
    rw [hnorm]
    have h := e.symm.toContinuousLinearMap.le_opNorm (e f)
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using h

/-- A positive lower constant depending solely on the fixed ordinal model. -/
def ordinalCofinalBlockLowerBound (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) : ℝ :=
  1 / (1 + ‖(ordinalCofinalBlockEquiv (𝕜 := 𝕜) γ hγ hc).symm.toContinuousLinearMap‖)

theorem ordinalCofinalBlockLowerBound_pos (γ : Ordinal.{0}) (hγ : IsSuccLimit γ)
    (hc : γ.card ≤ Cardinal.aleph0) : 0 < ordinalCofinalBlockLowerBound (𝕜 := 𝕜) γ hγ hc := by
  unfold ordinalCofinalBlockLowerBound
  positivity

private theorem lower_bound_of_inverse_bound {D a b : ℝ} (hD : 0 ≤ D)
    (hb : 0 ≤ b) (hab : a ≤ D * b) : (1 / (1 + D)) * a ≤ b := by
  have hd : 0 < 1 + D := by linarith
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_iff₀ hd).mpr
  nlinarith

theorem exists_ordinalCofinalBlockEmbedding_boundedBelow
    (γ : Ordinal.{0}) (hγ : IsSuccLimit γ) (hc : γ.card ≤ Cardinal.aleph0)
    (Q : ℕ → Type*) [∀ n, TopologicalSpace (Q n)] [∀ n, CompactSpace (Q n)]
    [∀ n, T2Space (Q n)] [∀ n, Countable (Q n)]
    (β : ℕ → Ordinal.{0}) (hβ : Monotone β)
    (hcof : ∀ α < γ, ∃ n, α ≤ β n)
    (hD : ∀ n, (ordinalDerived (univ : Set (Q n)) (β n)).Nonempty) :
    ∃ J : OrdinalContinuous 𝕜 (ω ^ γ) →L[𝕜] JLMS.CZeroSum 𝕜 (fun n => C(Q n, 𝕜)),
      ‖J‖ ≤ ‖(ordinalCofinalBlockEquiv (𝕜 := 𝕜) γ hγ hc).toContinuousLinearMap‖ ∧
      ∀ f, ordinalCofinalBlockLowerBound (𝕜 := 𝕜) γ hγ hc * ‖f‖ ≤ ‖J f‖ := by
  obtain ⟨J, hJ, hl⟩ := exists_ordinalCofinalBlockEmbedding (𝕜 := 𝕜) γ hγ hc Q β hβ hcof hD
  refine ⟨J, hJ, ?_⟩
  intro f
  exact lower_bound_of_inverse_bound (norm_nonneg _) (norm_nonneg (J f)) (hl f)

end Posets
