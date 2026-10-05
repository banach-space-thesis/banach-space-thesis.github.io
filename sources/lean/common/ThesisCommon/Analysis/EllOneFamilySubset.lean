import ThesisCommon.Analysis.LpOneFamilyOperators
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Contractive restriction and isometric zero extension for an arbitrary
subfamily of a genuine heterogeneous ell-one sum. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜] {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

def ellOneFamilyRestrictValue (A : Set I) (x : lp E 1) : lp (fun i : A => E i.val) 1 :=
  ⟨fun i => x i.val, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lpOneFamily_hasSum_norm x).summable.subtype A)⟩

theorem norm_ellOneFamilyRestrictValue_le (A : Set I) (x : lp E 1) :
    ‖ellOneFamilyRestrictValue A x‖ ≤ ‖x‖ := by
  have h := Summable.tsum_subtype_le (fun i => ‖x i‖) A (fun i => norm_nonneg _)
    (lpOneFamily_hasSum_norm x).summable
  simpa only [← (lpOneFamily_hasSum_norm x).tsum_eq,
    ← (lpOneFamily_hasSum_norm (ellOneFamilyRestrictValue A x)).tsum_eq] using h

def ellOneFamilyRestrict (A : Set I) : lp E 1 →L[𝕜] lp (fun i : A => E i.val) 1 :=
  LinearMap.mkContinuous
    { toFun := ellOneFamilyRestrictValue A
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa only [one_mul] using norm_ellOneFamilyRestrictValue_le A x)

@[simp] theorem ellOneFamilyRestrict_apply (A : Set I) (x : lp E 1) (i : A) :
    ellOneFamilyRestrict (𝕜 := 𝕜) A x i = x i.val := rfl

def ellOneFamilyExtendFunction (A : Set I) (x : lp (fun i : A => E i.val) 1) (i : I) : E i :=
  if hi : i ∈ A then x ⟨i, hi⟩ else 0

theorem ellOneFamilyExtendFunction_hasSum_norm (A : Set I)
    (x : lp (fun i : A => E i.val) 1) :
    HasSum (fun i => ‖ellOneFamilyExtendFunction A x i‖) ‖x‖ := by
  have hs : Function.support (fun i => ‖ellOneFamilyExtendFunction A x i‖) ⊆ A := by
    intro i hi
    by_contra hn
    simpa [ellOneFamilyExtendFunction, hn] using hi
  apply (hasSum_subtype_iff_of_support_subset hs).mp
  simpa only [Function.comp_def, ellOneFamilyExtendFunction, dif_pos (Subtype.property _)] using lpOneFamily_hasSum_norm x

def ellOneFamilyExtendValue (A : Set I) (x : lp (fun i : A => E i.val) 1) : lp E 1 :=
  ⟨ellOneFamilyExtendFunction A x, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (ellOneFamilyExtendFunction_hasSum_norm A x).summable)⟩

theorem norm_ellOneFamilyExtendValue (A : Set I) (x : lp (fun i : A => E i.val) 1) :
    ‖ellOneFamilyExtendValue A x‖ = ‖x‖ :=
  (lpOneFamily_hasSum_norm (ellOneFamilyExtendValue A x)).unique
    (ellOneFamilyExtendFunction_hasSum_norm A x)

def ellOneFamilyExtend (A : Set I) : lp (fun i : A => E i.val) 1 →L[𝕜] lp E 1 :=
  LinearMap.mkContinuous
    { toFun := ellOneFamilyExtendValue A
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change ellOneFamilyExtendFunction A (x+y) i =
          ellOneFamilyExtendFunction A x i + ellOneFamilyExtendFunction A y i
        by_cases hi : i ∈ A <;> simp [ellOneFamilyExtendFunction, hi]
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change ellOneFamilyExtendFunction A (c • x) i = c • ellOneFamilyExtendFunction A x i
        by_cases hi : i ∈ A <;> simp [ellOneFamilyExtendFunction, hi] }
    1 (fun x => by
      change ‖ellOneFamilyExtendValue A x‖ ≤ 1 * ‖x‖
      rw [norm_ellOneFamilyExtendValue, one_mul])

@[simp] theorem ellOneFamilyExtend_apply (A : Set I) (x : lp (fun i : A => E i.val) 1) (i : I) :
    ellOneFamilyExtend (𝕜 := 𝕜) A x i = if hi : i ∈ A then x ⟨i, hi⟩ else 0 := rfl

theorem ellOneFamilyRestrict_extend (A : Set I) :
    (ellOneFamilyRestrict (𝕜 := 𝕜) (E := E) A).comp (ellOneFamilyExtend A) =
      ContinuousLinearMap.id 𝕜 (lp (fun i : A => E i.val) 1) := by
  ext x i
  simp

theorem ellOneFamilyExtend_restrict_add_compl (A : Set I) :
    (ellOneFamilyExtend (𝕜 := 𝕜) (E := E) A).comp (ellOneFamilyRestrict A) +
      (ellOneFamilyExtend Aᶜ).comp (ellOneFamilyRestrict Aᶜ) =
        ContinuousLinearMap.id 𝕜 (lp E 1) := by
  ext x i
  by_cases hi : i ∈ A <;> simp [hi]

theorem norm_ellOneFamilyRestrict_le (A : Set I) :
    ‖ellOneFamilyRestrict (𝕜 := 𝕜) (E := E) A‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_ellOneFamilyExtend_le (A : Set I) :
    ‖ellOneFamilyExtend (𝕜 := 𝕜) (E := E) A‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon


