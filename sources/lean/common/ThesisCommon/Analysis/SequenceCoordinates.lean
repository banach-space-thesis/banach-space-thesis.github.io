import ThesisCommon.Analysis.SequenceSpaces

/-! Bounded coordinate evaluations for actual ℓp and c₀ spaces. -/
noncomputable section
open scoped ENNReal ZeroAtInfty
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {ι : Type*}

def lpCoordinate (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) : lp (fun _ : ι => X) p →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun x => x i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1
    (fun x => by
      simpa only [one_mul] using
        lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) x i)

@[simp] theorem lpCoordinate_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : ι)
    (x : lp (fun _ : ι => X) p) : lpCoordinate (𝕜 := 𝕜) p i x = x i := rfl

theorem norm_lpCoordinate_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) :
    ‖lpCoordinate (𝕜 := 𝕜) (X := X) p i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable [TopologicalSpace ι]

def cZeroCoordinate (i : ι) : C₀(ι, X) →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun x => x i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } 1
    (fun x => by simpa using BoundedContinuousFunction.norm_coe_le_norm x.toBCF i)

@[simp] theorem cZeroCoordinate_apply (i : ι) (x : C₀(ι, X)) :
    cZeroCoordinate (𝕜 := 𝕜) i x = x i := rfl

theorem norm_cZeroCoordinate_le (i : ι) : ‖cZeroCoordinate (𝕜 := 𝕜) (X := X) i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ThesisCommon
