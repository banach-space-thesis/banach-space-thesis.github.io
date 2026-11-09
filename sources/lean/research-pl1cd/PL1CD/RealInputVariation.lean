import PL1CD.ScalarOperatorVanishing

noncomputable section
open Filter
open scoped Topology BigOperators

namespace PL1CD.Variation
open PL1.ScalarRealification
variable (K : Type*) [RCLike K]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z]
  [NormedSpace ℝ Z] [IsScalarTower ℝ K Z]

def realInputOperator (T : HaarL1 K →L[K] Z) : HaarL1 ℝ →L[ℝ] Z :=
  (T.restrictScalars ℝ).comp (ofRealL1 K)

theorem levelSeminorm_realInput (M : ℕ → ℕ) (n : ℕ) (T : HaarL1 K →L[K] Z) :
    levelSeminorm ℝ Z M n (realInputOperator K T) = levelSeminorm K Z M n T := by
  change (Fintype.card (PL1.FiniteCoordinateKernels.Assignments
    (Finset.range (M (n + 1)))) : ℝ)⁻¹ * ∑ a, ‖T (ofRealL1 K
      (PL1.ExplicitMartingale.kernelL1 ℝ (M (n + 1))
        (PL1.FiniteCoordinateKernels.extend _ a) -
       PL1.ExplicitMartingale.kernelL1 ℝ (M n)
        (PL1.FiniteCoordinateKernels.extend _ a)))‖ = _
  simp_rw [map_sub (ofRealL1 K), ofRealL1_kernel]
  rfl

theorem endpointSeminorm_realInput (M N : ℕ → ℕ) (s : ℕ) (T : HaarL1 K →L[K] Z) :
    endpointSeminorm ℝ Z M N s (realInputOperator K T) = endpointSeminorm K Z M N s T := by
  simp only [endpointSeminorm, averageSeminorm_apply, levelSeminorm_realInput]

end PL1CD.Variation
