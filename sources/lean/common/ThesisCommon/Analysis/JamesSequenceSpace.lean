import ThesisCommon.Analysis.JamesPathNorms
import Mathlib.Analysis.Normed.Group.Seminorm

/-! The actual James sequence space: null scalar sequences with bounded
finite-path p-variation, equipped with the supremum of those path norms.
This fresh type does not inherit the c₀ supremum norm. For 1<p<∞ it is the
Jp model in Bird–Laustsen, Section 2.1. The construction also works for the
other Banach exponents; paper statements specify the required open interval.
-/
noncomputable section
open Filter Topology
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)

/-- Boundedness of all actual finite increasing path difference norms. -/
def HasBoundedJamesVariation (x : CZeroSum 𝕜) : Prop :=
  BddAbove (Set.range (fun s : JamesPath => ‖jamesPathMap 𝕜 p s x‖))

def jamesSequenceSubmodule : Submodule 𝕜 (CZeroSum 𝕜) where
  carrier := HasBoundedJamesVariation 𝕜 p
  zero_mem' := ⟨0, by rintro _ ⟨s, rfl⟩; simp⟩
  add_mem' := by
    rintro x y ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, ?_⟩
    rintro _ ⟨s, rfl⟩
    change ‖jamesPathMap 𝕜 p s (x + y)‖ ≤ C + D
    rw [map_add]
    exact (norm_add_le _ _).trans
      (add_le_add (hC (Set.mem_range_self s)) (hD (Set.mem_range_self s)))
  smul_mem' := by
    rintro c x ⟨C, hC⟩
    refine ⟨‖c‖ * C, ?_⟩
    rintro _ ⟨s, rfl⟩
    change ‖jamesPathMap 𝕜 p s (c • x)‖ ≤ ‖c‖ * C
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (Set.mem_range_self s)) (norm_nonneg c)

/-- Null sequences with bounded p-variation; the norm is installed below. -/
def JamesSequenceSpace := ↥(jamesSequenceSubmodule 𝕜 p)

namespace JamesSequenceSpace
variable {𝕜 p}

instance : AddCommGroup (JamesSequenceSpace 𝕜 p) :=
  inferInstanceAs (AddCommGroup ↥(jamesSequenceSubmodule 𝕜 p))
instance : Module 𝕜 (JamesSequenceSpace 𝕜 p) :=
  inferInstanceAs (Module 𝕜 ↥(jamesSequenceSubmodule 𝕜 p))
instance : CoeFun (JamesSequenceSpace 𝕜 p) (fun _ => ℕ → 𝕜) := ⟨fun x => x.val⟩

@[ext] theorem ext {x y : JamesSequenceSpace 𝕜 p} (h : ∀ n, x n = y n) : x = y := by
  apply Subtype.ext
  ext n
  exact h n

@[simp] theorem zero_apply (n : ℕ) : (0 : JamesSequenceSpace 𝕜 p) n = 0 := rfl
@[simp] theorem add_apply (x y : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    (x + y) n = x n + y n := rfl
@[simp] theorem neg_apply (x : JamesSequenceSpace 𝕜 p) (n : ℕ) : (-x) n = -x n := rfl
@[simp] theorem sub_apply (x y : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    (x - y) n = x n - y n := rfl
@[simp] theorem smul_apply (c : 𝕜) (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    (c • x) n = c • x n := rfl

/-- The supremum of finite increasing path p-difference norms. -/
def variationNorm (x : JamesSequenceSpace 𝕜 p) : ℝ :=
  ⨆ s : JamesPath, ‖jamesPathMap 𝕜 p s x.val‖

theorem path_norm_le_variationNorm (x : JamesSequenceSpace 𝕜 p) (s : JamesPath) :
    ‖jamesPathMap 𝕜 p s x.val‖ ≤ variationNorm x :=
  le_ciSup x.property s

theorem variationNorm_nonneg (x : JamesSequenceSpace 𝕜 p) : 0 ≤ variationNorm x :=
  (norm_nonneg _).trans (path_norm_le_variationNorm x (JamesPath.two 0 1 Nat.zero_lt_one))

theorem variationNorm_add_le (x y : JamesSequenceSpace 𝕜 p) :
    variationNorm (x + y) ≤ variationNorm x + variationNorm y := by
  apply ciSup_le
  intro s
  change ‖jamesPathMap 𝕜 p s (x.val + y.val)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans
    (add_le_add (path_norm_le_variationNorm x s) (path_norm_le_variationNorm y s))

/-- Null convergence makes the difference seminorm separate points and dominate coordinates. -/
theorem norm_apply_le_variationNorm (x : JamesSequenceSpace 𝕜 p) (n : ℕ) :
    ‖x n‖ ≤ variationNorm x := by
  have hz : Tendsto (fun m => x m) atTop (𝓝 0) := by
    simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using x.val.zero_at_infty'
  have ht : Tendsto (fun m => ‖x n - x m‖) atTop (𝓝 ‖x n‖) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hz).norm
  apply le_of_tendsto ht
  filter_upwards [eventually_gt_atTop n] with m hm
  exact (jamesPath_two_difference_le 𝕜 p x.val n m hm).trans
    (path_norm_le_variationNorm x (JamesPath.two n m hm))

theorem variationNorm_eq_zero {x : JamesSequenceSpace 𝕜 p}
    (h : variationNorm x = 0) : x = 0 := by
  apply ext
  intro n
  apply norm_eq_zero.mp
  exact le_antisymm ((norm_apply_le_variationNorm x n).trans_eq h) (norm_nonneg _)

instance instNormedAddCommGroup : NormedAddCommGroup (JamesSequenceSpace 𝕜 p) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := variationNorm
      map_zero' := by simp [variationNorm]
      neg' := fun x => by
        change (⨆ s : JamesPath, ‖jamesPathMap 𝕜 p s (-x.val)‖) = variationNorm x
        simp only [map_neg, norm_neg, variationNorm]
      add_le' := variationNorm_add_le
      eq_zero_of_map_eq_zero' := fun _ h => variationNorm_eq_zero h }

theorem norm_def (x : JamesSequenceSpace 𝕜 p) :
    ‖x‖ = ⨆ s : JamesPath, ‖jamesPathMap 𝕜 p s x.val‖ := rfl

/-- The exact displayed Bird–Laustsen norm, with natural indices starting at zero. -/
theorem norm_eq_iSup_path_variation (hp : p.val ≠ ∞) (x : JamesSequenceSpace 𝕜 p) :
    ‖x‖ = ⨆ s : JamesPath,
      (∑ j : Fin s.length,
        ‖x (s.index j.castSucc) - x (s.index j.succ)‖ ^ p.val.toReal) ^
        (1 / p.val.toReal) := by
  rw [norm_def]
  exact iSup_congr fun s => jamesPathMap_norm 𝕜 p hp s x.val

instance instNormedSpace : NormedSpace 𝕜 (JamesSequenceSpace 𝕜 p) where
  norm_smul_le c x := by
    change variationNorm (c • x) ≤ ‖c‖ * variationNorm x
    apply ciSup_le
    intro s
    change ‖jamesPathMap 𝕜 p s (c • x.val)‖ ≤ _
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (path_norm_le_variationNorm x s) (norm_nonneg c)

theorem path_norm_le (x : JamesSequenceSpace 𝕜 p) (s : JamesPath) :
    ‖jamesPathMap 𝕜 p s x.val‖ ≤ ‖x‖ := path_norm_le_variationNorm x s

theorem norm_le {x : JamesSequenceSpace 𝕜 p} {C : ℝ}
    (h : ∀ s : JamesPath, ‖jamesPathMap 𝕜 p s x.val‖ ≤ C) : ‖x‖ ≤ C :=
  ciSup_le h

theorem norm_apply_le (x : JamesSequenceSpace 𝕜 p) (n : ℕ) : ‖x n‖ ≤ ‖x‖ :=
  norm_apply_le_variationNorm x n

theorem tendsto_zero (x : JamesSequenceSpace 𝕜 p) :
    Tendsto (fun n => x n) atTop (𝓝 0) := by
  simpa only [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] using x.val.zero_at_infty'

/-- Forgetting the variation bound is contractive into the actual c₀ norm. -/
theorem norm_toCZero_le (x : JamesSequenceSpace 𝕜 p) : ‖x.val‖ ≤ ‖x‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg x)).mpr
  exact norm_apply_le x

def toCZero : JamesSequenceSpace 𝕜 p →L[𝕜] CZeroSum 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => x.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by simpa only [one_mul] using norm_toCZero_le x)

@[simp] theorem toCZero_apply (x : JamesSequenceSpace 𝕜 p) :
    toCZero (𝕜 := 𝕜) (p := p) x = x.val := rfl

theorem norm_toCZero_operator_le : ‖toCZero (𝕜 := 𝕜) (p := p)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def coordinate (n : ℕ) : JamesSequenceSpace 𝕜 p →L[𝕜] 𝕜 :=
  (cZeroCoordinate n).comp toCZero

@[simp] theorem coordinate_apply (n : ℕ) (x : JamesSequenceSpace 𝕜 p) :
    coordinate (𝕜 := 𝕜) (p := p) n x = x n := rfl

theorem norm_coordinate_le (n : ℕ) : ‖coordinate (𝕜 := 𝕜) (p := p) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [coordinate_apply, one_mul] using norm_apply_le x n

end JamesSequenceSpace
end ThesisCommon
