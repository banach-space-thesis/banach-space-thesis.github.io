import BanachIsometric.RealEvenFunctionalRigidity
import BanachIsometric.RealOddNormRigidity

/-! The genuine real even-section normed consequence. The original norm
and real scalar action are retained in the inner-product witness, with no
external Gromov, Lie-group torsion or initial quadraticity premise. -/

namespace BanachIsometric

open Set Metric
open scoped Topology NNReal

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem real_even_norm_positiveGaugeData
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ V)
    (hmetric : MetricSubspaceHomogeneity ℝ V n) :
    Nonempty (MetricGeometry.PositiveGaugeData (norm : V → ℝ)) := by
  apply positiveGaugeData_of_real_even_sections real_norm_algebraicPositiveHomogeneous
    hn heven hdim (real_norm_localSphereLipschitz n)
  intro E F hE hF
  letI : Module.Finite ℝ E := Module.finite_of_finrank_pos (by rw [hE]; omega)
  letI : Module.Finite ℝ F := Module.finite_of_finrank_pos (by rw [hF]; omega)
  obtain ⟨T⟩ := hmetric E F (by rw [← Module.finrank_eq_rank, hE]) (by rw [← Module.finrank_eq_rank, hF])
  let U := T.toRealLinearIsometryEquiv
  exact ⟨U.toLinearEquiv, fun x => U.norm_map x⟩

theorem real_even_normedCorollaryB
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hdim : (n : Cardinal) < Module.rank ℝ V)
    (hmetric : MetricSubspaceHomogeneity ℝ V n) : HasInnerProductForGivenScalarAction ℝ V := by
  obtain ⟨D⟩ := real_even_norm_positiveGaugeData hn heven hdim hmetric
  exact ⟨D.innerProductSpaceOfNorm, rfl⟩

end
end BanachIsometric
