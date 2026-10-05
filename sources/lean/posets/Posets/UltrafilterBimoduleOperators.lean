import Posets.UltrafilterBimoduleLimits

/-! Selector pullback operators and bounded matrix coefficients for Lemma 8.2. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜]

theorem bimodule_unitVector_norm_le {P : Type*} (p : P) : ‖unitVector 𝕜 p‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro x
  change ‖if x.val = p then (1 : 𝕜) else 0‖ ≤ 1
  split_ifs <;> simp

theorem selector_discrete_tendsto (n : ℕ) :
    Tendsto (fun x : Discrete RowDomain => (⟨selector n x.val⟩ : Discrete ColumnDomain))
      (cocompact _) (cocompact _) := by
  rw [cocompact_eq_cofinite, cocompact_eq_cofinite]
  have hv : Function.Injective (fun x : Discrete RowDomain => x.val) := by
    rintro ⟨x⟩ ⟨y⟩ h
    cases h
    rfl
  have hm : Function.Injective (Discrete.mk : ColumnDomain → Discrete ColumnDomain) := by
    intro x y h
    exact congrArg Discrete.val h
  exact hm.tendsto_cofinite.comp ((selector_tendsto_cofinite n).comp hv.tendsto_cofinite)

/-- Pulling a null function back along a finite-to-one selector gives a null function. -/
def selectorPullbackVector (n : ℕ) (f : CZeroOn 𝕜 ColumnDomain) : CZeroOn 𝕜 RowDomain where
  toFun x := f ⟨selector n x.val⟩
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := (zero_at_infty f).comp (selector_discrete_tendsto n)

theorem selectorPullbackVector_norm_le (n : ℕ) (f : CZeroOn 𝕜 ColumnDomain) :
    ‖selectorPullbackVector n f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact f.toBCF.norm_coe_le_norm ⟨selector n x.val⟩

/-- The operators S_n used to separate the ultrafilter matrix coefficients. -/
def selectorPullbackOperator (n : ℕ) : OffDiagonal 𝕜 :=
  ({toFun := selectorPullbackVector n
    map_add' := by intro f g; ext x; rfl
    map_smul' := by intro a f; ext x; rfl} :
      CZeroOn 𝕜 ColumnDomain →ₗ[𝕜] CZeroOn 𝕜 RowDomain).mkContinuous 1
    (fun f => by simpa only [one_mul] using selectorPullbackVector_norm_le n f)

@[simp] theorem selectorPullbackOperator_apply (n : ℕ)
    (f : CZeroOn 𝕜 ColumnDomain) (x : Discrete RowDomain) :
    selectorPullbackOperator n f x = f ⟨selector n x.val⟩ := rfl

theorem selectorPullbackOperator_norm_le (n : ℕ) :
    ‖selectorPullbackOperator (𝕜 := 𝕜) n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f => by simpa only [one_mul] using selectorPullbackVector_norm_le n f)

theorem selectedMatrixCoefficient_bound (n : ℕ) (T : OffDiagonal 𝕜) (x : RowDomain) :
    ‖T (unitVector 𝕜 (selector n x)) ⟨x⟩‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖T (unitVector 𝕜 (selector n x))‖ :=
      (T (unitVector 𝕜 (selector n x))).toBCF.norm_coe_le_norm _
    _ ≤ ‖T‖ * ‖unitVector 𝕜 (selector n x)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left
      (bimodule_unitVector_norm_le (𝕜 := 𝕜) _) (norm_nonneg T)
    _ = ‖T‖ := mul_one _

def selectedMatrixCoefficients (n : ℕ) (T : OffDiagonal 𝕜) : Discrete RowDomain →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => T (unitVector 𝕜 (selector n x.val)) x) ‖T‖
    (fun x => selectedMatrixCoefficient_bound n T x.val)

theorem selectedMatrixCoefficients_norm_le (n : ℕ) (T : OffDiagonal 𝕜) :
    ‖selectedMatrixCoefficients n T‖ ≤ ‖T‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg T)).mpr
  intro x
  exact selectedMatrixCoefficient_bound n T x.val

def selectedMatrixCoefficientMap (n : ℕ) :
    OffDiagonal 𝕜 →L[𝕜] (Discrete RowDomain →ᵇ 𝕜) := by
  let f : OffDiagonal 𝕜 →ₗ[𝕜] (Discrete RowDomain →ᵇ 𝕜) :=
    { toFun := selectedMatrixCoefficients (𝕜 := 𝕜) n
      map_add' := by intro T S; ext x; rfl
      map_smul' := by intro a T; ext x; rfl }
  have hf : ∀ T : OffDiagonal 𝕜, ‖f T‖ ≤ 1 * ‖T‖ := by
    intro T
    change ‖selectedMatrixCoefficients (𝕜 := 𝕜) n T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using selectedMatrixCoefficients_norm_le (𝕜 := 𝕜) n T
  exact ⟨f, AddMonoidHomClass.continuous_of_bound f 1 hf⟩

/-- F_n reads the selected matrix entry and takes its row-ultrafilter limit. -/
def ultrafilterMatrixFunctional (U : Ultrafilter RowDomain) (n : ℕ) : OffDiagonal 𝕜 →L[𝕜] 𝕜 :=
  (ultrafilterEvaluation U).comp (selectedMatrixCoefficientMap (𝕜 := 𝕜) n)

@[simp] theorem ultrafilterMatrixFunctional_apply (U : Ultrafilter RowDomain) (n : ℕ)
    (T : OffDiagonal 𝕜) :
    ultrafilterMatrixFunctional (𝕜 := 𝕜) U n T =
      limUnder (U : Filter RowDomain) (fun x => T (unitVector 𝕜 (selector n x)) ⟨x⟩) := rfl

theorem tendsto_ultrafilterMatrixFunctional (U : Ultrafilter RowDomain) (n : ℕ)
    (T : OffDiagonal 𝕜) :
    Tendsto (fun x => T (unitVector 𝕜 (selector n x)) ⟨x⟩) (U : Filter RowDomain)
      (𝓝 (ultrafilterMatrixFunctional (𝕜 := 𝕜) U n T)) :=
  tendsto_ultrafilter_bounded U _ (selectedMatrixCoefficient_bound n T)

end Posets
