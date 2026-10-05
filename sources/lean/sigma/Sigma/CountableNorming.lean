import Sigma.FunctionSpaces
import ThesisCommon.Analysis.NormingSequence
import ThesisCommon.Analysis.ProductNorming
import Mathlib.Data.Countable.Defs

noncomputable section
namespace SigmaNonprimarity
open ThesisCommon
open scoped BoundedContinuousFunction

local instance submoduleNormedGroup {I : Type*} [TopologicalSpace I]
    (S : Submodule ℝ (I →ᵇ ℝ)) : NormedAddCommGroup S := inferInstance
local instance submoduleNormedSpace {I : Type*} [TopologicalSpace I]
    (S : Submodule ℝ (I →ᵇ ℝ)) : NormedSpace ℝ S := inferInstance

def submoduleEvaluation {I : Type*} [TopologicalSpace I]
    (S : Submodule ℝ (I →ᵇ ℝ)) (p : I) : S →L[ℝ] ℝ :=
  ({ toFun := fun f => f.val p
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : S →ₗ[ℝ] ℝ).mkContinuous
    1 (by intro f; simpa using f.val.norm_coe_le_norm p)

theorem submoduleEvaluation_oneNorming {I : Type*} [TopologicalSpace I]
    (S : Submodule ℝ (I →ᵇ ℝ)) (p : ℕ → I) (hp : Function.Surjective p) :
    IsCNorming (E := S) (fun n => submoduleEvaluation S (p n)) 1 := by
  let e : ℕ → S →L[ℝ] ℝ := fun n => submoduleEvaluation S (p n)
  have he (n) : ‖e n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa using f.val.norm_coe_le_norm (p n)
  refine ⟨zero_lt_one, le_rfl, he, ?_⟩
  intro f
  rw [one_mul]
  have hb := evaluations_bddAbove e he f
  have hn : 0 ≤ ⨆ n, |e n f| := (abs_nonneg _).trans (le_ciSup hb 0)
  apply (BoundedContinuousFunction.norm_le hn).mpr
  intro q
  obtain ⟨n, rfl⟩ := hp q
  change ‖e n f‖ ≤ _
  rw [Real.norm_eq_abs]
  exact le_ciSup hb n

/-- Every subspace of bounded functions on a countable domain has a countable 1-norming set. -/
theorem countable_submodule_has_countable_norming {I : Type*} [TopologicalSpace I]
    [Countable I] [Nonempty I] (S : Submodule ℝ (I →ᵇ ℝ)) :
    ∃ e : ℕ → S →L[ℝ] ℝ, IsCNorming (E := S) e 1 := by
  obtain ⟨p, hp⟩ := exists_surjective_nat I
  exact ⟨_, submoduleEvaluation_oneNorming S p hp⟩

theorem submodule_has_countable_norming (S : Submodule ℝ Ambient) :
    ∃ e : ℕ → S →L[ℝ] ℝ, IsCNorming (E := S) e 1 :=
  countable_submodule_has_countable_norming S

theorem candidate_has_countable_norming (B Atilde : Set (Set Point)) :
    ∃ e : ℕ → CandidateX B Atilde →L[ℝ] ℝ,
      IsCNorming (E := CandidateX B Atilde) e 1 := by
  obtain ⟨a, ha⟩ := submodule_has_countable_norming (CylinderJL Atilde)
  obtain ⟨b, hb⟩ := submodule_has_countable_norming (antisymmetricJL B)
  exact product_has_one_norming ha hb

end SigmaNonprimarity
