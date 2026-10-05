import ThesisCommon.Analysis.SchauderSolidity
import Mathlib.Analysis.Normed.Group.Seminorm

/-! The vector-valued sum X(Y) of Section 3.2, represented by actual
sequences y : ℕ → Y whose coordinate norms are the coefficients of a vector
in X. The norm is the norm of that vector. Convergent Schauder expansions
give exactly the series definition in the manuscript.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ThesisCommon
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The manuscript's membership condition: the scalar coordinate norms
are the coefficient sequence of an actual vector in the outer space. -/
def MemSchauderSum (b : NormalizedSchauderBasis 𝕜 X) {Y : Type*}
    [NormedAddCommGroup Y] (y : ℕ → Y) : Prop :=
  ∃ x : X, ∀ n, b.coord n x = (‖y n‖ : 𝕜)

variable (b : NormalizedSchauderBasis 𝕜 X) [CompleteSpace X]
variable (hb : b.IsOneUnconditional) (Y : Type*)
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The genuine sequence space is closed under the pointwise vector-space operations. -/
def schauderSumSubmodule : Submodule 𝕜 (ℕ → Y) where
  carrier := MemSchauderSum b
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

/-- X(Y) with the chosen normalized one-unconditional basis on X. -/
def SchauderSum := ↥(schauderSumSubmodule b hb Y)

namespace SchauderSum
variable {b hb Y}

instance : AddCommGroup (SchauderSum b hb Y) :=
  inferInstanceAs (AddCommGroup ↥(schauderSumSubmodule b hb Y))
instance : Module 𝕜 (SchauderSum b hb Y) :=
  inferInstanceAs (Module 𝕜 ↥(schauderSumSubmodule b hb Y))
instance : CoeFun (SchauderSum b hb Y) (fun _ => ℕ → Y) := ⟨fun y => y.val⟩

@[ext] theorem ext {y z : SchauderSum b hb Y} (h : ∀ n, y n = z n) : y = z :=
  Subtype.ext (funext h)

@[simp] theorem zero_apply (n : ℕ) : (0 : SchauderSum b hb Y) n = 0 := rfl
@[simp] theorem add_apply (y z : SchauderSum b hb Y) (n : ℕ) : (y + z) n = y n + z n := rfl
@[simp] theorem neg_apply (y : SchauderSum b hb Y) (n : ℕ) : (-y) n = -y n := rfl
@[simp] theorem sub_apply (y z : SchauderSum b hb Y) (n : ℕ) : (y - z) n = y n - z n := rfl
@[simp] theorem smul_apply (c : 𝕜) (y : SchauderSum b hb Y) (n : ℕ) : (c • y) n = c • y n := rfl

/-- The unique vector in X with coefficients equal to the coordinate norms. -/
def normVector (y : SchauderSum b hb Y) : X := y.property.choose

@[simp] theorem coord_normVector (y : SchauderSum b hb Y) (n : ℕ) :
    b.coord n (normVector y) = (‖y n‖ : 𝕜) := y.property.choose_spec n

theorem normVector_eq (y : SchauderSum b hb Y) (x : X)
    (hx : ∀ n, b.coord n x = (‖y n‖ : 𝕜)) : normVector y = x :=
  b.ext (fun n => (coord_normVector y n).trans (hx n).symm)

@[simp] theorem normVector_zero : normVector (0 : SchauderSum b hb Y) = 0 := by
  apply normVector_eq
  simp

@[simp] theorem normVector_neg (y : SchauderSum b hb Y) : normVector (-y) = normVector y := by
  apply normVector_eq
  simp

@[simp] theorem normVector_smul (c : 𝕜) (y : SchauderSum b hb Y) :
    normVector (c • y) = (‖c‖ : 𝕜) • normVector y := by
  apply normVector_eq
  intro n
  simp only [map_smul, coord_normVector, smul_apply, norm_smul, RCLike.ofReal_mul,
    smul_eq_mul]

/-- This norm is exactly ||sum_n ||y_n|| e_n||. -/
def basisNorm (y : SchauderSum b hb Y) : ℝ := ‖normVector y‖

theorem basisNorm_add_le (y z : SchauderSum b hb Y) :
    basisNorm (y + z) ≤ basisNorm y + basisNorm z := by
  apply le_trans (b.norm_le_of_coord_le hb (x := normVector (y + z))
    (y := normVector y + normVector z) ?_) (norm_add_le _ _)
  intro n
  rw [map_add, coord_normVector, coord_normVector, coord_normVector,
    ← RCLike.ofReal_add]
  simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), add_apply,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact norm_add_le _ _

theorem basisNorm_eq_zero {y : SchauderSum b hb Y} (hy : basisNorm y = 0) : y = 0 := by
  have hv : normVector y = 0 := norm_eq_zero.mp hy
  apply ext
  intro n
  have hn := coord_normVector y n
  rw [hv, map_zero] at hn
  have he : ‖y n‖ = 0 := by
    apply RCLike.ofReal_injective (K := 𝕜)
    simpa only [RCLike.ofReal_zero] using hn.symm
  exact norm_eq_zero.mp he

instance instNormedAddCommGroup : NormedAddCommGroup (SchauderSum b hb Y) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := basisNorm
      map_zero' := by simp [basisNorm]
      neg' := fun y => by simp [basisNorm]
      add_le' := basisNorm_add_le
      eq_zero_of_map_eq_zero' := fun _ h => basisNorm_eq_zero h }

theorem norm_def (y : SchauderSum b hb Y) : ‖y‖ = ‖normVector y‖ := rfl

instance instNormedSpace : NormedSpace 𝕜 (SchauderSum b hb Y) where
  norm_smul_le c y := by
    rw [norm_def, normVector_smul, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg c)]
    exact le_rfl

/-- Each coordinate has norm at most the norm in X(Y). -/
theorem norm_apply_le (y : SchauderSum b hb Y) (n : ℕ) : ‖y n‖ ≤ ‖y‖ := by
  have h := b.coord_le_norm hb n (normVector y)
  simpa only [coord_normVector, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] using h

/-- The sum-norm vector is represented by the source's convergent series. -/
theorem normVector_expansion (y : SchauderSum b hb Y) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (‖y n‖ : 𝕜) • b.vector n)
      atTop (𝓝 (normVector y)) := by
  simpa only [coord_normVector] using b.expansion (normVector y)

end SchauderSum
end ThesisCommon
