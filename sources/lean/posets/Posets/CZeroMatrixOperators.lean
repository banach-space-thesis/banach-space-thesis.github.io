import Posets.ScalarMatrixRows

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology ThesisCommon
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {P : Type*} [Nonempty P]

def rowNorm (M : P → P → 𝕜) : ℝ := ⨆ s, ∑' t, ‖M s t‖

omit [Nonempty P] in
theorem rowNorm_bdd (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M) :
    BddAbove (Set.range (fun s => ∑' t, ‖M s t‖)) := by
  obtain ⟨C, hC⟩ := hM.2
  exact ⟨C, by rintro _ ⟨s, rfl⟩; exact hC s⟩

theorem rowNorm_nonneg (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M) : 0 ≤ rowNorm M :=
  (tsum_nonneg (fun t => norm_nonneg (M (Classical.arbitrary P) t))).trans
    (le_ciSup (rowNorm_bdd M hM) (Classical.arbitrary P))

def cZeroMatrixValue (M : P → P → 𝕜) (f : CZeroOn 𝕜 P) (s : Discrete P) : 𝕜 :=
  ∑' t, M s.val t * f ⟨t⟩

omit [Nonempty P] in
theorem cZeroMatrix_summable (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (f : CZeroOn 𝕜 P) (s : P) : Summable (fun t => M s t * f ⟨t⟩) := by
  apply ((hM.1 s).mul_right ‖f‖).of_norm_bounded
  intro t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.toBCF.norm_coe_le_norm _) (norm_nonneg _)

omit [Nonempty P] in
theorem cZeroMatrixValue_bound (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (f : CZeroOn 𝕜 P) (s : Discrete P) :
    ‖cZeroMatrixValue M f s‖ ≤ rowNorm M * ‖f‖ := by
  have hbound : ∀ t, ‖M s.val t * f ⟨t⟩‖ ≤ ‖M s.val t‖ * ‖f‖ := by
    intro t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.toBCF.norm_coe_le_norm _) (norm_nonneg _)
  calc
    ‖cZeroMatrixValue M f s‖ ≤ ∑' t, ‖M s.val t‖ * ‖f‖ :=
      tsum_of_norm_bounded ((hM.1 s.val).mul_right ‖f‖).hasSum hbound
    _ = (∑' t, ‖M s.val t‖) * ‖f‖ := tsum_mul_right
    _ ≤ rowNorm M * ‖f‖ := mul_le_mul_of_nonneg_right
      (le_ciSup (rowNorm_bdd M hM) s.val) (norm_nonneg _)

def cZeroMatrixBCF (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (f : CZeroOn 𝕜 P) : Discrete P →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (cZeroMatrixValue M f)
    (rowNorm M * ‖f‖) (cZeroMatrixValue_bound M hM f)

def cZeroMatrixToBCF (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M) :
    CZeroOn 𝕜 P →L[𝕜] (Discrete P →ᵇ 𝕜) :=
  ({toFun := cZeroMatrixBCF M hM
    map_add' := by
      intro f g
      ext s
      change (∑' t, M s.val t * (f ⟨t⟩ + g ⟨t⟩)) =
        (∑' t, M s.val t * f ⟨t⟩) + ∑' t, M s.val t * g ⟨t⟩
      simp_rw [mul_add]
      exact (cZeroMatrix_summable M hM f s.val).tsum_add (cZeroMatrix_summable M hM g s.val)
    map_smul' := by
      intro a f
      ext s
      change (∑' t, M s.val t * (a * f ⟨t⟩)) = a * ∑' t, M s.val t * f ⟨t⟩
      simp_rw [mul_left_comm (M s.val _) a]
      exact tsum_mul_left} : CZeroOn 𝕜 P →ₗ[𝕜] (Discrete P →ᵇ 𝕜)).mkContinuous
    (rowNorm M) (fun f => (BoundedContinuousFunction.norm_le
      (mul_nonneg (rowNorm_nonneg M hM) (norm_nonneg f))).mpr (cZeroMatrixValue_bound M hM f))

theorem cZeroMatrixToBCF_unit (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (t : P) (s : Discrete P) : cZeroMatrixToBCF M hM (unitVector 𝕜 t) s = M s.val t := by
  change (∑' p, M s.val p * (if p = t then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single t]
  · simp
  · intro p hp
    simp [hp]

def cZeroMatrixColumn (M : P → P → 𝕜) (hcols : ZeroColumnsOn 𝕜 M) (t : P) : CZeroOn 𝕜 P where
  toFun s := M s.val t
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite]
    exact (hcols t).comp (show Function.Injective (Discrete.val : Discrete P → P) from
      fun ⟨_⟩ ⟨_⟩ h => congrArg Discrete.mk h).tendsto_cofinite

theorem cZeroMatrixToBCF_truncation_mem (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (hcols : ZeroColumnsOn 𝕜 M) (f : CZeroOn 𝕜 P) (F : Finset (Discrete P)) :
    cZeroMatrixToBCF M hM (discreteTruncation F f) ∈
      Set.range (ZeroAtInftyContinuousMap.toBCF : CZeroOn 𝕜 P → (Discrete P →ᵇ 𝕜)) := by
  refine ⟨∑ p ∈ F, f p • cZeroMatrixColumn M hcols p.val, ?_⟩
  ext s
  change (∑ p ∈ F, f p • cZeroMatrixColumn M hcols p.val) s = _
  rw [czero_finset_sum_apply]
  simp only [discreteTruncation, map_sum, map_smul, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, ZeroAtInftyContinuousMap.smul_apply,
    discreteUnit_eq_unitVector, cZeroMatrixToBCF_unit]
  rfl

theorem cZeroMatrixToBCF_mem (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (hcols : ZeroColumnsOn 𝕜 M) (f : CZeroOn 𝕜 P) :
    cZeroMatrixToBCF M hM f ∈
      Set.range (ZeroAtInftyContinuousMap.toBCF : CZeroOn 𝕜 P → (Discrete P →ᵇ 𝕜)) :=
  ZeroAtInftyContinuousMap.isClosed_range_toBCF.mem_of_tendsto
    ((cZeroMatrixToBCF M hM).continuous.continuousAt.tendsto.comp (discreteTruncation_tendsto f))
    (Filter.Eventually.of_forall (cZeroMatrixToBCF_truncation_mem M hM hcols f))

def cZeroMatrixFunction (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (hcols : ZeroColumnsOn 𝕜 M) (f : CZeroOn 𝕜 P) : CZeroOn 𝕜 P where
  toContinuousMap := (cZeroMatrixToBCF M hM f).toContinuousMap
  zero_at_infty' := by
    obtain ⟨g, hg⟩ := cZeroMatrixToBCF_mem M hM hcols f
    change Tendsto (cZeroMatrixToBCF M hM f) _ _
    rw [← hg]
    exact zero_at_infty g

def cZeroMatrixOperator (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (hcols : ZeroColumnsOn 𝕜 M) : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P :=
  ({toFun := cZeroMatrixFunction M hM hcols
    map_add' := by
      intro f g
      ext s
      exact congrArg (fun b : Discrete P →ᵇ 𝕜 => b s) ((cZeroMatrixToBCF M hM).map_add f g)
    map_smul' := by
      intro a f
      ext s
      exact congrArg (fun b : Discrete P →ᵇ 𝕜 => b s) ((cZeroMatrixToBCF M hM).map_smul a f)} :
      CZeroOn 𝕜 P →ₗ[𝕜] CZeroOn 𝕜 P).mkContinuous (rowNorm M) (fun f =>
        (BoundedContinuousFunction.norm_le
          (mul_nonneg (rowNorm_nonneg M hM) (norm_nonneg f))).mpr (cZeroMatrixValue_bound M hM f))

theorem scalarMatrix_cZeroMatrixOperator (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (hcols : ZeroColumnsOn 𝕜 M) : scalarMatrix 𝕜 (cZeroMatrixOperator M hM hcols) = M := by
  funext s t
  exact cZeroMatrixToBCF_unit M hM t ⟨s⟩

theorem norm_cZeroMatrixOperator (M : P → P → 𝕜) (hM : BoundedRowsOn 𝕜 M)
    (hcols : ZeroColumnsOn 𝕜 M) : ‖cZeroMatrixOperator M hM hcols‖ = rowNorm M := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (rowNorm_nonneg M hM)
    intro f
    exact (BoundedContinuousFunction.norm_le
      (mul_nonneg (rowNorm_nonneg M hM) (norm_nonneg f))).mpr (cZeroMatrixValue_bound M hM f)
  · apply ciSup_le
    intro s
    have h := scalarMatrix_row_bound (cZeroMatrixOperator M hM hcols) s
    rwa [scalarMatrix_cZeroMatrixOperator] at h

theorem norm_eq_rowNorm_scalarMatrix (T : CZeroOn 𝕜 P →L[𝕜] CZeroOn 𝕜 P) :
    ‖T‖ = rowNorm (scalarMatrix 𝕜 T) := by
  have heq : cZeroMatrixOperator (scalarMatrix 𝕜 T)
      (scalarMatrix_boundedRows T) (scalarMatrix_zeroColumns T) = T :=
    scalarMatrix_injective (scalarMatrix_cZeroMatrixOperator _ _ _)
  calc
    ‖T‖ = ‖cZeroMatrixOperator (scalarMatrix 𝕜 T)
      (scalarMatrix_boundedRows T) (scalarMatrix_zeroColumns T)‖ := congrArg norm heq.symm
    _ = _ := norm_cZeroMatrixOperator _ (scalarMatrix_boundedRows T) (scalarMatrix_zeroColumns T)

theorem proposition_6_15_proof (𝕜 : Type) [RCLike 𝕜] (P : Type) [Countable P] [Infinite P] :
    Proposition_6_15 𝕜 P := by
  constructor
  · intro T
    exact ⟨scalarMatrix_boundedRows T, scalarMatrix_zeroColumns T, norm_eq_rowNorm_scalarMatrix T⟩
  · intro M hM hcols
    exact ⟨cZeroMatrixOperator M hM hcols, scalarMatrix_cZeroMatrixOperator M hM hcols⟩

end Posets
