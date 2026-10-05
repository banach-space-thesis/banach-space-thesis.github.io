import ThesisCommon.Analysis.SequenceSpaces

/-! Coordinate maps on vector-valued c₀, realized as C₀ over a discrete index set.
The proofs establish vanishing at infinity as well as the supremum norm bounds.
They expand the same zero-extension idea used for scalar c₀ in JLMS.CZeroBlocks.
-/
noncomputable section
open Filter Topology
open scoped ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
variable [TopologicalSpace κ] [DiscreteTopology κ]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Domination by a multiple of a null family preserves vanishing at infinity. -/
def cZeroOfDominated (x : C₀(ι, X)) (f : ι → Y) {C : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ C * ‖x i‖) : C₀(ι, Y) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := squeeze_zero_norm hf (by
    simpa using tendsto_const_nhds.mul x.zero_at_infty'.norm)

theorem norm_cZeroOfDominated_le (x : C₀(ι, X)) (f : ι → Y) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C * ‖x i‖) : ‖cZeroOfDominated x f hf‖ ≤ C * ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg x))).mpr
  intro i
  exact (hf i).trans (mul_le_mul_of_nonneg_left
    (BoundedContinuousFunction.norm_coe_le_norm x.toBCF i) hC)

/-- A uniformly bounded family acts diagonally on the actual c₀ space. -/
def cZeroDiagonal (F : ι → X →L[𝕜] Y) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i, ‖F i‖ ≤ C) : C₀(ι, X) →L[𝕜] C₀(ι, Y) :=
  LinearMap.mkContinuous
    { toFun := fun x => cZeroOfDominated x (fun i => F i (x i))
        (fun i => ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _)))
      map_add' := by
        intro x y
        ext i
        change F i (x i + y i) = F i (x i) + F i (y i)
        exact map_add _ _ _
      map_smul' := by
        intro a x
        ext i
        change F i (a • x i) = a • F i (x i)
        exact map_smul _ _ _ }
    C (fun x => norm_cZeroOfDominated_le x _ hC (fun i =>
      ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _))))

@[simp] theorem cZeroDiagonal_apply (F : ι → X →L[𝕜] Y) (C : ℝ) (hC hF)
    (x : C₀(ι, X)) (i : ι) : cZeroDiagonal F C hC hF x i = F i (x i) := rfl

theorem norm_cZeroDiagonal_le (F : ι → X →L[𝕜] Y) (C : ℝ) (hC hF) :
    ‖cZeroDiagonal F C hC hF‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC _

/-- Restriction along an injection preserves a null family: inverse images of
finite exceptional sets are finite. -/
def cZeroRead (e : ι ↪ κ) (x : C₀(κ, X)) : C₀(ι, X) where
  toFun i := x (e i)
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    have ht := e.injective.tendsto_cofinite
    rw [← cocompact_eq_cofinite ι, ← cocompact_eq_cofinite κ] at ht
    exact x.zero_at_infty'.comp ht

theorem norm_cZeroRead_le (e : ι ↪ κ) (x : C₀(κ, X)) : ‖cZeroRead e x‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro i
  exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF (e i)

def cZeroRestrict (e : ι ↪ κ) : C₀(κ, X) →L[𝕜] C₀(ι, X) :=
  LinearMap.mkContinuous
    { toFun := cZeroRead e
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa using norm_cZeroRead_le e x)

@[simp] theorem cZeroRestrict_apply (e : ι ↪ κ) (x : C₀(κ, X)) (i : ι) :
    cZeroRestrict (𝕜 := 𝕜) e x i = x (e i) := rfl

theorem norm_cZeroRestrict_le (e : ι ↪ κ) :
    ‖cZeroRestrict (𝕜 := 𝕜) (X := X) e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Insertion on the image of an injection preserves vanishing at infinity:
every exceptional set is contained in the image of a finite exceptional set. -/
def cZeroInsert (e : ι ↪ κ) (x : C₀(ι, X)) : C₀(κ, X) where
  toFun := Function.extend e x 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    classical
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hx := Metric.tendsto_nhds.mp x.zero_at_infty' ε hε
    rw [cocompact_eq_cofinite] at hx ⊢
    have hbad : {i : ι | ¬ dist (x i) 0 < ε}.Finite := mem_cofinite.mp hx
    filter_upwards [(hbad.image e).compl_mem_cofinite] with k hk
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      rw [e.injective.extend_apply]
      by_contra hi
      exact hk ⟨i, hi, rfl⟩
    · simp [Function.extend_apply' _ _ _ h, hε]

theorem norm_cZeroInsert_le (e : ι ↪ κ) (x : C₀(ι, X)) : ‖cZeroInsert e x‖ ≤ ‖x‖ := by
  classical
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  intro k
  change ‖Function.extend e x 0 k‖ ≤ ‖x‖
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    rw [e.injective.extend_apply]
    exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF i
  · simp [Function.extend_apply' _ _ _ h]

def cZeroExtend (e : ι ↪ κ) : C₀(ι, X) →L[𝕜] C₀(κ, X) := by
  classical
  refine LinearMap.mkContinuous
    { toFun := cZeroInsert e
      map_add' := ?_
      map_smul' := ?_ } 1 (fun x => by simpa using norm_cZeroInsert_le e x)
  · intro x y
    ext k
    change Function.extend e (x + y) 0 k = Function.extend e x 0 k + Function.extend e y 0 k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  · intro a x
    ext k
    change Function.extend e (a • x) 0 k = a • Function.extend e x 0 k
    by_cases h : ∃ i, e i = k
    · obtain ⟨i, rfl⟩ := h
      simp [e.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

@[simp] theorem cZeroExtend_apply_image (e : ι ↪ κ) (x : C₀(ι, X)) (i : ι) :
    cZeroExtend (𝕜 := 𝕜) e x (e i) = x i := by
  simp [cZeroExtend, cZeroInsert, e.injective.extend_apply]

theorem norm_cZeroExtend_le (e : ι ↪ κ) :
    ‖cZeroExtend (𝕜 := 𝕜) (X := X) e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem cZeroRestrict_comp_extend (e : ι ↪ κ) :
    (cZeroRestrict (𝕜 := 𝕜) (X := X) e).comp (cZeroExtend e) =
      ContinuousLinearMap.id 𝕜 C₀(ι, X) := by
  ext x i
  simp

end ThesisCommon
