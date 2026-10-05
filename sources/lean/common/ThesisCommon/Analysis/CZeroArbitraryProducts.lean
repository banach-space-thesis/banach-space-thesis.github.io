import ThesisCommon.Analysis.LpArbitraryProducts
import ThesisCommon.Analysis.CZeroOperators

/-! Actual arbitrary-index flattening and reindexing for c₀. Vanishing at
infinity follows from finite exceptional rows and finite exceptional entries
inside each row; both flattening and its inverse preserve the supremum norm.
-/
noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Δ Ε Ζ Γ : Type*}
variable [TopologicalSpace Δ] [DiscreteTopology Δ]
  [TopologicalSpace Ε] [DiscreteTopology Ε]
  [TopologicalSpace Ζ] [DiscreteTopology Ζ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

def cZeroReindexIsometry (e : Δ ≃ Ε) : C₀(Δ, X) ≃ₗᵢ[𝕜] C₀(Ε, X) where
  toFun := cZeroRead e.symm.toEmbedding
  invFun := cZeroRead e.toEmbedding
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  left_inv := by intro x; ext i; exact congrArg x (e.symm_apply_apply i)
  right_inv := by intro x; ext j; exact congrArg x (e.apply_symm_apply j)
  norm_map' := by
    intro x
    apply (norm_cZeroRead_le e.symm.toEmbedding x).antisymm
    have h := norm_cZeroRead_le e.toEmbedding (cZeroRead e.symm.toEmbedding x)
    have heq : cZeroRead e.toEmbedding (cZeroRead e.symm.toEmbedding x) = x := by
      ext i
      exact congrArg x (e.symm_apply_apply i)
    rwa [heq] at h

@[simp] theorem cZeroReindexIsometry_apply (e : Δ ≃ Ε) (x : C₀(Δ, X)) (j : Ε) :
    cZeroReindexIsometry (𝕜 := 𝕜) (X := X) e x j = x (e.symm j) := rfl

@[simp] theorem cZeroReindexIsometry_symm_apply (e : Δ ≃ Ε) (x : C₀(Ε, X)) (i : Δ) :
    (cZeroReindexIsometry (𝕜 := 𝕜) (X := X) e).symm x i = x (e i) := rfl

theorem cZero_arbitrary_finite_norm_exception (x : C₀(Δ, X)) {ε : ℝ} (hε : 0 < ε) :
    {i | ¬ ‖x i‖ < ε}.Finite := by
  have h := Metric.tendsto_nhds.mp x.zero_at_infty' ε hε
  rw [cocompact_eq_cofinite] at h
  simpa only [dist_zero_right] using mem_cofinite.mp h

variable (φ : Δ × Ε ≃ Ζ)

def cZeroProductFlattenValue (x : C₀(Δ, C₀(Ε, X))) : C₀(Ζ, X) where
  toFun z := x (φ.symm z).1 (φ.symm z).2
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [cocompact_eq_cofinite]
    let A := {i | ¬ ‖x i‖ < ε}
    let B := fun i => {j | ¬ ‖x i j‖ < ε}
    have hA : A.Finite := cZero_arbitrary_finite_norm_exception x hε
    have hB (i : Δ) : (B i).Finite := cZero_arbitrary_finite_norm_exception (x i) hε
    have hbad : (⋃ i ∈ A, (fun j => φ (i, j)) '' B i).Finite :=
      hA.biUnion (fun i _ => (hB i).image (fun j => φ (i, j)))
    filter_upwards [hbad.compl_mem_cofinite] with z hz
    rw [dist_zero_right]
    by_contra hzlarge
    have hi : (φ.symm z).1 ∈ A := by
      intro hsmall
      exact hzlarge ((BoundedContinuousFunction.norm_coe_le_norm
        (x (φ.symm z).1).toBCF (φ.symm z).2).trans_lt hsmall)
    have hj : (φ.symm z).2 ∈ B (φ.symm z).1 := hzlarge
    exact hz (Set.mem_iUnion.mpr ⟨(φ.symm z).1,
      Set.mem_iUnion.mpr ⟨hi, ⟨(φ.symm z).2, hj, φ.apply_symm_apply z⟩⟩⟩)

theorem norm_cZeroProductFlattenValue_le (x : C₀(Δ, C₀(Ε, X))) :
    ‖cZeroProductFlattenValue φ x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro z
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (x (φ.symm z).1).toBCF (φ.symm z).2).trans
      (BoundedContinuousFunction.norm_coe_le_norm x.toBCF (φ.symm z).1)

def cZeroProductUnflattenValue (x : C₀(Ζ, X)) : C₀(Δ, C₀(Ε, X)) where
  toFun i := cZeroRead (productCoordinateEmbedding φ i) x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    rw [cocompact_eq_cofinite]
    let B := {z | ¬ ‖x z‖ < ε / 2}
    have hB : B.Finite := cZero_arbitrary_finite_norm_exception x (half_pos hε)
    filter_upwards [(hB.image (fun z => (φ.symm z).1)).compl_mem_cofinite] with i hi
    have hpoint (j : Ε) : ‖x (φ (i, j))‖ < ε / 2 := by
      by_contra hlarge
      exact hi ⟨φ (i, j), hlarge, by simp⟩
    have hnorm : ‖cZeroRead (productCoordinateEmbedding φ i) x‖ ≤ ε / 2 := by
      apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
      intro j
      exact (hpoint j).le
    simpa only [dist_zero_right] using hnorm.trans_lt (half_lt_self hε)

theorem norm_cZeroProductUnflattenValue_le (x : C₀(Ζ, X)) :
    ‖cZeroProductUnflattenValue φ x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro i
  exact norm_cZeroRead_le (productCoordinateEmbedding φ i) x

theorem cZeroProductUnflatten_flatten (x : C₀(Δ, C₀(Ε, X))) :
    cZeroProductUnflattenValue φ (cZeroProductFlattenValue φ x) = x := by
  ext i j
  change x (φ.symm (φ (i, j))).1 (φ.symm (φ (i, j))).2 = x i j
  rw [φ.symm_apply_apply]

theorem norm_cZeroProductFlattenValue (x : C₀(Δ, C₀(Ε, X))) :
    ‖cZeroProductFlattenValue φ x‖ = ‖x‖ := by
  apply le_antisymm (norm_cZeroProductFlattenValue_le φ x)
  have h := norm_cZeroProductUnflattenValue_le φ (cZeroProductFlattenValue φ x)
  rwa [cZeroProductUnflatten_flatten] at h

def cZeroProductFlattenIsometry : C₀(Δ, C₀(Ε, X)) ≃ₗᵢ[𝕜] C₀(Ζ, X) where
  toFun := cZeroProductFlattenValue φ
  invFun := cZeroProductUnflattenValue φ
  map_add' := by intros; ext z; rfl
  map_smul' := by intros; ext z; rfl
  left_inv := cZeroProductUnflatten_flatten φ
  right_inv := by
    intro x
    ext z
    change x (φ ((φ.symm z).1, (φ.symm z).2)) = x z
    simp only [Prod.mk.eta, φ.apply_symm_apply]
  norm_map' := norm_cZeroProductFlattenValue φ

@[simp] theorem cZeroProductFlattenIsometry_apply (x : C₀(Δ, C₀(Ε, X))) (z : Ζ) :
    cZeroProductFlattenIsometry (𝕜 := 𝕜) (X := X) φ x z = x (φ.symm z).1 (φ.symm z).2 := rfl

@[simp] theorem cZeroProductFlattenIsometry_apply_image
    (x : C₀(Δ, C₀(Ε, X))) (i : Δ) (j : Ε) :
    cZeroProductFlattenIsometry (𝕜 := 𝕜) (X := X) φ x (φ (i, j)) = x i j := by
  simp only [cZeroProductFlattenIsometry_apply, φ.symm_apply_apply]

@[simp] theorem cZeroProductFlattenIsometry_symm_apply
    (x : C₀(Ζ, X)) (i : Δ) (j : Ε) :
    (cZeroProductFlattenIsometry (𝕜 := 𝕜) (X := X) φ).symm x i j = x (φ (i, j)) := rfl

def cZeroArbitraryAbsorbCountableIsometry [Infinite Γ] :
    C₀(Γ, C₀(ℕ, X)) ≃ₗᵢ[𝕜] C₀(Γ, X) :=
  cZeroProductFlattenIsometry (infiniteCountableProductEquiv Γ)

def cZeroArbitrarySequenceSelfIsometry [Infinite Γ] :
    C₀(Γ, X) ≃ₗᵢ[𝕜] C₀(ℕ, C₀(Γ, X)) :=
  (cZeroProductFlattenIsometry
    ((Equiv.prodComm ℕ Γ).trans (infiniteCountableProductEquiv Γ))).symm

end ThesisCommon
