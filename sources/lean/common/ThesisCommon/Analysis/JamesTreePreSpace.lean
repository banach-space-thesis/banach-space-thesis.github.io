import ThesisCommon.Analysis.JamesTreeTestNorms
import Mathlib.Analysis.Normed.Group.Seminorm

/-! Genuine c₀₀ of the dyadic tree with the supremum of disjoint-segment
ℓp norms. The segment family is explicit, and its only stipulated law is
admissibility of singleton segments, used for definiteness of the norm.
No factorisation, primariness, or subtree conclusion is a field of the space.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon

set_option linter.unusedVariables false in
/-- A fresh type for c₀₀, carrying the chosen segment norm rather than a pre-existing norm.
The parameters p and S intentionally index the norm, not the underlying coefficient type. -/
def JamesTreePreSpace (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
    (S : JamesTreeSegmentFamily) := DyadicTreeNode →₀ 𝕜

namespace JamesTreePreSpace
variable {𝕜 : Type*} [RCLike 𝕜] {p : BanachExponent} {S : JamesTreeSegmentFamily}

instance : AddCommGroup (JamesTreePreSpace 𝕜 p S) :=
  inferInstanceAs (AddCommGroup (DyadicTreeNode →₀ 𝕜))
instance : Module 𝕜 (JamesTreePreSpace 𝕜 p S) :=
  inferInstanceAs (Module 𝕜 (DyadicTreeNode →₀ 𝕜))

def coefficients (a : JamesTreePreSpace 𝕜 p S) : DyadicTreeNode →₀ 𝕜 := a
instance : CoeFun (JamesTreePreSpace 𝕜 p S) (fun _ => DyadicTreeNode → 𝕜) :=
  ⟨fun a => coefficients a⟩

@[ext] theorem ext {a b : JamesTreePreSpace 𝕜 p S} (h : ∀ t, a t = b t) : a = b :=
  Finsupp.ext h

@[simp] theorem zero_apply (t : DyadicTreeNode) : (0 : JamesTreePreSpace 𝕜 p S) t = 0 := rfl
@[simp] theorem add_apply (a b : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) :
    (a + b) t = a t + b t := rfl
@[simp] theorem sub_apply (a b : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) :
    (a - b) t = a t - b t := rfl
@[simp] theorem smul_apply (c : 𝕜) (a : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) :
    (c • a) t = c • a t := rfl

def segmentNorm (a : JamesTreePreSpace 𝕜 p S) : ℝ :=
  ⨆ T : JamesTreeTest S, ‖jamesTreeTestMap 𝕜 p T (coefficients a)‖

theorem testNorms_bddAbove (a : JamesTreePreSpace 𝕜 p S) :
    BddAbove (Set.range (fun T : JamesTreeTest S =>
      ‖jamesTreeTestMap 𝕜 p T (coefficients a)‖)) := by
  refine ⟨∑ t ∈ (coefficients a).support, ‖a t‖, ?_⟩
  rintro _ ⟨T, rfl⟩
  exact jamesTreeTestMap_norm_le_mass 𝕜 p T (coefficients a)

theorem test_norm_le_segmentNorm (a : JamesTreePreSpace 𝕜 p S) (T : JamesTreeTest S) :
    ‖jamesTreeTestMap 𝕜 p T (coefficients a)‖ ≤ segmentNorm a :=
  le_ciSup (testNorms_bddAbove a) T

theorem norm_apply_le_segmentNorm (a : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) :
    ‖a t‖ ≤ segmentNorm a :=
  (jamesTree_singleton_coordinate_le 𝕜 p S (coefficients a) t).trans
    (test_norm_le_segmentNorm a (JamesTreeTest.singleton S t))

theorem segmentNorm_add_le (a b : JamesTreePreSpace 𝕜 p S) :
    segmentNorm (a + b) ≤ segmentNorm a + segmentNorm b := by
  apply ciSup_le
  intro T
  change ‖jamesTreeTestMap 𝕜 p T (coefficients a + coefficients b)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans
    (add_le_add (test_norm_le_segmentNorm a T) (test_norm_le_segmentNorm b T))

theorem segmentNorm_eq_zero {a : JamesTreePreSpace 𝕜 p S} (ha : segmentNorm a = 0) : a = 0 := by
  apply ext
  intro t
  apply norm_eq_zero.mp
  exact le_antisymm ((norm_apply_le_segmentNorm a t).trans_eq ha) (norm_nonneg _)

instance instNormedAddCommGroup : NormedAddCommGroup (JamesTreePreSpace 𝕜 p S) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := segmentNorm
      map_zero' := by simp [segmentNorm, coefficients]
      neg' := fun a => by
        change (⨆ T : JamesTreeTest S, ‖jamesTreeTestMap 𝕜 p T (-coefficients a)‖) = segmentNorm a
        simp only [map_neg, norm_neg, segmentNorm]
      add_le' := segmentNorm_add_le
      eq_zero_of_map_eq_zero' := fun _ h => segmentNorm_eq_zero h }

instance instNormedSpace : NormedSpace 𝕜 (JamesTreePreSpace 𝕜 p S) where
  norm_smul_le c a := by
    change segmentNorm (c • a) ≤ ‖c‖ * segmentNorm a
    apply ciSup_le
    intro T
    change ‖jamesTreeTestMap 𝕜 p T (c • coefficients a)‖ ≤ _
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (test_norm_le_segmentNorm a T) (norm_nonneg c)

theorem norm_def (a : JamesTreePreSpace 𝕜 p S) :
    ‖a‖ = ⨆ T : JamesTreeTest S, ‖jamesTreeTestMap 𝕜 p T (coefficients a)‖ := rfl

/-- Exact finite-p disjoint-segment formula from the manuscript. -/
theorem norm_eq_iSup_segment_sums (hp : p.val ≠ ∞) (a : JamesTreePreSpace 𝕜 p S) :
    ‖a‖ = ⨆ T : JamesTreeTest S,
      (∑ j : Fin T.count, ‖∑ t ∈ T.segment j, a t‖ ^ p.val.toReal) ^
        (1 / p.val.toReal) := by
  rw [norm_def]
  exact iSup_congr fun T => jamesTreeTestMap_norm 𝕜 p hp T (coefficients a)

theorem test_norm_le (a : JamesTreePreSpace 𝕜 p S) (T : JamesTreeTest S) :
    ‖jamesTreeTestMap 𝕜 p T (coefficients a)‖ ≤ ‖a‖ := test_norm_le_segmentNorm a T

theorem norm_le {a : JamesTreePreSpace 𝕜 p S} {C : ℝ}
    (h : ∀ T : JamesTreeTest S, ‖jamesTreeTestMap 𝕜 p T (coefficients a)‖ ≤ C) : ‖a‖ ≤ C :=
  ciSup_le h

theorem norm_apply_le (a : JamesTreePreSpace 𝕜 p S) (t : DyadicTreeNode) : ‖a t‖ ≤ ‖a‖ :=
  norm_apply_le_segmentNorm a t

theorem norm_le_mass (a : JamesTreePreSpace 𝕜 p S) :
    ‖a‖ ≤ ∑ t ∈ (coefficients a).support, ‖a t‖ :=
  norm_le (fun T => jamesTreeTestMap_norm_le_mass 𝕜 p T (coefficients a))

def single (t : DyadicTreeNode) (c : 𝕜) : JamesTreePreSpace 𝕜 p S := Finsupp.single t c

@[simp] theorem single_apply (t u : DyadicTreeNode) (c : 𝕜) :
    single (p := p) (S := S) t c u = if t = u then c else 0 :=
  Finsupp.single_apply

@[simp] theorem norm_single (t : DyadicTreeNode) (c : 𝕜) :
    ‖single (p := p) (S := S) t c‖ = ‖c‖ := by
  apply le_antisymm
  · apply norm_le
    exact fun T => jamesTreeTestMap_single_norm_le 𝕜 p T t c
  · simpa only [single_apply, if_pos rfl] using
      norm_apply_le (single (p := p) (S := S) t c) t

def coordinate (t : DyadicTreeNode) : JamesTreePreSpace 𝕜 p S →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun a => a t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun a => by simpa only [one_mul] using norm_apply_le a t)

@[simp] theorem coordinate_apply (t : DyadicTreeNode) (a : JamesTreePreSpace 𝕜 p S) :
    coordinate (𝕜 := 𝕜) (p := p) (S := S) t a = a t := rfl

theorem norm_coordinate_le (t : DyadicTreeNode) :
    ‖coordinate (𝕜 := 𝕜) (p := p) (S := S) t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end JamesTreePreSpace
end ThesisCommon
