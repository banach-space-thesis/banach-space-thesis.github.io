import NonCalkinAlgebra.MatrixClosure
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D]

def HasFiniteColumnSupport (T : CoefficientSpace D →L[ℂ] CoefficientSpace D) : Prop :=
  ∃ F : Finset ℕ, ∀ j ∉ F, ∀ d : D, T (lp.single 1 j d) = 0

theorem finiteMatrixSpan_hasFiniteColumnSupport
    {T : CoefficientSpace D →L[ℂ] CoefficientSpace D} (hT : T ∈ finiteMatrixSpan D) :
    HasFiniteColumnSupport D T := by
  classical
  change T ∈ Submodule.span ℂ (matrixGenerators D) at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨i, k, d, rfl⟩ := hT
    refine ⟨{k}, ?_⟩
    intro j hj e
    have hjk : j ≠ k := by simpa only [Finset.mem_singleton] using hj
    simp [theta_apply, lp.single_apply, hjk, hjk.symm]
  | zero => exact ⟨∅, fun j hj d => rfl⟩
  | add T U hT hU ihT ihU =>
    obtain ⟨F, hF⟩ := ihT
    obtain ⟨G, hG⟩ := ihU
    refine ⟨F ∪ G, ?_⟩
    intro j hj d
    have hnot := Finset.notMem_union.mp hj
    simp [hF j hnot.1 d, hG j hnot.2 d]
  | smul c T hT ih =>
    obtain ⟨F, hF⟩ := ih
    exact ⟨F, fun j hj d => by simp [hF j hj d]⟩

theorem finiteMatrixSpan_annihilates_diagonal
    {T : CoefficientSpace D →L[ℂ] CoefficientSpace D} (hT : T ∈ finiteMatrixSpan D) :
    ∃ j : ℕ, T * scalarMatrixUnit D j j = 0 := by
  classical
  obtain ⟨F, hF⟩ := finiteMatrixSpan_hasFiniteColumnSupport D hT
  let j := F.sup id + 1
  have hj : j ∉ F := by
    intro h
    have hle : j ≤ F.sup id := Finset.le_sup (f := id) h
    exact Nat.not_succ_le_self _ hle
  refine ⟨j, ?_⟩
  ext x n
  have h := congrArg (fun y : CoefficientSpace D => y n) (hF j hj (x j))
  simpa only [ContinuousLinearMap.mul_apply, scalarMatrixUnit, theta_apply, one_mul,
    ContinuousLinearMap.zero_apply] using h

variable [NormOneClass D]

/-- The nonunitality part of Proposition 5.1. This proves absence of any
internal identity, not just non-membership of the ambient identity.
-/
theorem matrixClosure_has_no_identity :
    ¬ ∃ U : CoefficientSpace D →L[ℂ] CoefficientSpace D, U ∈ matrixClosure D ∧
      ∀ T ∈ matrixClosure D, U * T = T ∧ T * U = T := by
  rintro ⟨U, hU, hunit⟩
  have hcl : U ∈ closure (finiteMatrixSpan D :
      Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) := hU
  obtain ⟨T, hT, hdist⟩ :=
    (Metric.mem_closure_iff (a := U) (s := (finiteMatrixSpan D :
      Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)))).mp hcl (1 / 2) (by norm_num)
  obtain ⟨j, hj⟩ := finiteMatrixSpan_annihilates_diagonal D hT
  let e := scalarMatrixUnit D j j
  have heJ : e ∈ matrixClosure D := theta_mem_matrixClosure D j j 1
  have heNorm : ‖e‖ = 1 := norm_scalarMatrixUnit D j j
  have hprod : (U - T) * e = e := by
    rw [sub_mul, (hunit e heJ).1, hj, sub_zero]
  have hbound : (1 : ℝ) ≤ ‖U - T‖ := by
    calc
      1 = ‖e‖ := heNorm.symm
      _ = ‖(U - T) * e‖ := congrArg norm hprod.symm
      _ ≤ ‖U - T‖ * ‖e‖ := norm_mul_le (U - T) e
      _ = ‖U - T‖ := by rw [heNorm, mul_one]
  have hsmall : ‖U - T‖ < (1 / 2 : ℝ) := by
    simpa only [dist_eq_norm] using hdist
  linarith

theorem one_not_mem_matrixClosure :
    (1 : CoefficientSpace D →L[ℂ] CoefficientSpace D) ∉ matrixClosure D := by
  intro h
  exact matrixClosure_has_no_identity D ⟨1, h, fun T hT => ⟨one_mul T, mul_one T⟩⟩

end NonCalkinAlgebra
