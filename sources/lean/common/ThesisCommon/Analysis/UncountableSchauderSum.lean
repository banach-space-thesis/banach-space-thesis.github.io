import ThesisCommon.Analysis.UncountableSchauderSolidity
import Mathlib.Analysis.Normed.Group.Seminorm

/-! The arbitrary-index vector-valued sum E(Γ,Y) of Section 4. Its elements
are actual families y : Γ → Y whose coordinate norms are the coefficients
of a vector in E. The norm is the norm of that vector. The expansion is a
net over all finite subsets of Γ, with no countability assumption on Γ.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 Γ X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The manuscript's membership condition: the scalar coordinate norms
are the coefficient sequence of an actual vector in the outer space. -/
def MemUncountableSchauderSum (b : NormalizedSchauderFamily 𝕜 Γ X) {Y : Type*}
    [NormedAddCommGroup Y] (y : Γ → Y) : Prop :=
  ∃ x : X, ∀ n, b.coord n x = (‖y n‖ : 𝕜)

variable (b : NormalizedSchauderFamily 𝕜 Γ X) [CompleteSpace X]
variable (hb : b.IsOneUnconditional) (Y : Type*)
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The genuine family space is closed under the pointwise vector-space operations. -/
def uncountableSchauderSumSubmodule : Submodule 𝕜 (Γ → Y) where
  carrier := MemUncountableSchauderSum b
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro y z ⟨x, hx⟩ ⟨w, hw⟩
    obtain ⟨v, hv, _⟩ := b.exists_of_coord_domination hb (x + w)
      (fun n => (‖y n + z n‖ : 𝕜)) (by
        intro n
        rw [map_add, hx, hw, ← RCLike.ofReal_add]
        simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
          abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact norm_add_le _ _)
    exact ⟨v, hv⟩
  smul_mem' := by
    rintro c y ⟨x, hx⟩
    refine ⟨(‖c‖ : 𝕜) • x, ?_⟩
    intro n
    simp only [map_smul, hx, Pi.smul_apply, norm_smul, RCLike.ofReal_mul, smul_eq_mul]

/-- E(Γ,Y) with a normalized one-unconditional family on the outer space. -/
def UncountableSchauderSum := ↥(uncountableSchauderSumSubmodule b hb Y)

namespace UncountableSchauderSum
variable {b hb Y}

instance : AddCommGroup (UncountableSchauderSum b hb Y) :=
  inferInstanceAs (AddCommGroup ↥(uncountableSchauderSumSubmodule b hb Y))
instance : Module 𝕜 (UncountableSchauderSum b hb Y) :=
  inferInstanceAs (Module 𝕜 ↥(uncountableSchauderSumSubmodule b hb Y))
instance : CoeFun (UncountableSchauderSum b hb Y) (fun _ => Γ → Y) := ⟨fun y => y.val⟩

@[ext] theorem ext {y z : UncountableSchauderSum b hb Y} (h : ∀ n, y n = z n) : y = z :=
  Subtype.ext (funext h)

@[simp] theorem zero_apply (n : Γ) : (0 : UncountableSchauderSum b hb Y) n = 0 := rfl
@[simp] theorem add_apply (y z : UncountableSchauderSum b hb Y) (n : Γ) : (y + z) n = y n + z n := rfl
@[simp] theorem neg_apply (y : UncountableSchauderSum b hb Y) (n : Γ) : (-y) n = -y n := rfl
@[simp] theorem sub_apply (y z : UncountableSchauderSum b hb Y) (n : Γ) : (y - z) n = y n - z n := rfl
@[simp] theorem smul_apply (c : 𝕜) (y : UncountableSchauderSum b hb Y) (n : Γ) : (c • y) n = c • y n := rfl

/-- The unique outer vector with coefficients equal to the coordinate norms. -/
def normVector (y : UncountableSchauderSum b hb Y) : X := y.property.choose

@[simp] theorem coord_normVector (y : UncountableSchauderSum b hb Y) (n : Γ) :
    b.coord n (normVector y) = (‖y n‖ : 𝕜) := y.property.choose_spec n

theorem normVector_eq (y : UncountableSchauderSum b hb Y) (x : X)
    (hx : ∀ n, b.coord n x = (‖y n‖ : 𝕜)) : normVector y = x :=
  b.ext (fun n => (coord_normVector y n).trans (hx n).symm)

@[simp] theorem normVector_zero : normVector (0 : UncountableSchauderSum b hb Y) = 0 := by
  apply normVector_eq
  simp

@[simp] theorem normVector_neg (y : UncountableSchauderSum b hb Y) : normVector (-y) = normVector y := by
  apply normVector_eq
  simp

@[simp] theorem normVector_smul (c : 𝕜) (y : UncountableSchauderSum b hb Y) :
    normVector (c • y) = (‖c‖ : 𝕜) • normVector y := by
  apply normVector_eq
  intro n
  simp only [map_smul, coord_normVector, smul_apply, norm_smul, RCLike.ofReal_mul,
    smul_eq_mul]

/-- This norm is exactly ||sum_n ||y_n|| e_n||. -/
def basisNorm (y : UncountableSchauderSum b hb Y) : ℝ := ‖normVector y‖

theorem basisNorm_add_le (y z : UncountableSchauderSum b hb Y) :
    basisNorm (y + z) ≤ basisNorm y + basisNorm z := by
  apply le_trans (b.norm_le_of_coord_le hb (x := normVector (y + z))
    (y := normVector y + normVector z) ?_) (norm_add_le _ _)
  intro n
  rw [map_add, coord_normVector, coord_normVector, coord_normVector,
    ← RCLike.ofReal_add]
  simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), add_apply,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact norm_add_le _ _

theorem basisNorm_eq_zero {y : UncountableSchauderSum b hb Y} (hy : basisNorm y = 0) : y = 0 := by
  have hv : normVector y = 0 := norm_eq_zero.mp hy
  apply ext
  intro n
  have hn := coord_normVector y n
  rw [hv, map_zero] at hn
  have he : ‖y n‖ = 0 := by
    apply RCLike.ofReal_injective (K := 𝕜)
    simpa only [RCLike.ofReal_zero] using hn.symm
  exact norm_eq_zero.mp he

instance instNormedAddCommGroup : NormedAddCommGroup (UncountableSchauderSum b hb Y) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := basisNorm
      map_zero' := by simp [basisNorm]
      neg' := fun y => by simp [basisNorm]
      add_le' := basisNorm_add_le
      eq_zero_of_map_eq_zero' := fun _ h => basisNorm_eq_zero h }

theorem norm_def (y : UncountableSchauderSum b hb Y) : ‖y‖ = ‖normVector y‖ := rfl

instance instNormedSpace : NormedSpace 𝕜 (UncountableSchauderSum b hb Y) where
  norm_smul_le c y := by
    rw [norm_def, normVector_smul, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg c)]
    exact le_rfl

/-- Each coordinate has norm at most the norm in X(Y). -/
theorem norm_apply_le (y : UncountableSchauderSum b hb Y) (n : Γ) : ‖y n‖ ≤ ‖y‖ := by
  have h := b.coord_le_norm hb n (normVector y)
  simpa only [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] using h

/-- The sum-norm vector is the limit of the source's finite-subset sum net. -/
theorem normVector_expansion (y : UncountableSchauderSum b hb Y) :
    Tendsto (fun F : Finset Γ => ∑ n ∈ F, (‖y n‖ : 𝕜) • b.vector n)
      atTop (𝓝 (normVector y)) := by
  simpa only [coord_normVector] using b.expansion_tendsto (normVector y)

end UncountableSchauderSum
end ThesisCommon

