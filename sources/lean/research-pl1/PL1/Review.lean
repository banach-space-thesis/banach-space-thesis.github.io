import PL1

/-!
Human-review entry point. The four main claims below are propositions, not
proved theorems. The two BanLat bridges at the end are proved theorems.
Run this file to obtain expanded definitions and their actual axiom lists.
-/

noncomputable section

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print PL1.intervalMeasure
#print PL1.IntervalL1
#print PL1.Ell2
#print PL1.Ell1
#print PL1.UnderlyingReal
#print PL1.underlyingRealNormedSpace
#print PL1.projectionBound
#print PL1.WeaklyConverges
#print PL1.HasSchurProperty
#print PL1.IsDunfordPettis
#print PL1.IsProjection
#print PL1.ContainsIsomorphicCopy
#print PL1.HasRadonNikodymProperty
#print PL1.HasEquivalentRealLatticeNorm
#print PL1.TheoremASpec
#print PL1.TheoremBSpec
#print PL1.TheoremAStatement
#print PL1.TheoremBStatement
#print PL1.TheoremARealStatement
#print PL1.TheoremAComplexStrongStatement
#print PL1.TheoremBRealStatement
#print PL1.TheoremBComplexStrongStatement
#print PL1.MainTheoremsStatement

-- These ask Lean for actual standard-space instances, without assuming them.
example : NormedSpace ℝ (PL1.IntervalL1 ℝ) := inferInstance
example : NormedSpace ℂ (PL1.IntervalL1 ℂ) := inferInstance
example : CompleteSpace (PL1.IntervalL1 ℝ) := inferInstance
example : CompleteSpace (PL1.IntervalL1 ℂ) := inferInstance
example : CompleteSpace (PL1.Ell2 ℝ) := inferInstance
example : CompleteSpace (PL1.Ell2 ℂ) := inferInstance
example : NormedSpace ℝ (PL1.UnderlyingReal ℂ (PL1.IntervalL1 ℂ)) := inferInstance

-- The norm of the underlying real type is definitionally the original norm.
example (x : PL1.IntervalL1 ℂ) :
    ‖(show PL1.UnderlyingReal ℂ (PL1.IntervalL1 ℂ) from x)‖ = ‖x‖ := rfl

#check PL1.hasEquivalentRealLatticeNorm_of_continuousLinearEquiv
#check PL1.not_nonempty_continuousLinearEquiv_of_not_hasEquivalentRealLatticeNorm
#print axioms PL1.hasEquivalentRealLatticeNorm_of_continuousLinearEquiv
#print axioms PL1.not_nonempty_continuousLinearEquiv_of_not_hasEquivalentRealLatticeNorm

-- This audits definitions only: it does not turn the four targets into proofs.
#print axioms PL1.MainTheoremsStatement
