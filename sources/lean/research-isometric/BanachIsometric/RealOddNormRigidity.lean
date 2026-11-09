import BanachIsometric.RealOddFunctionalTorsion
import BanachIsometric.Statements

/-! The real normed odd-section consequence of the actual geometric proof.
It is conditional on the displayed compact-body topology premise and makes
no claim about the even-section Banach/Gromov theorem. Original norm and
real scalar multiplication are retained exactly in the inner-product witness. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem real_norm_algebraicPositiveHomogeneous : AlgebraicPositiveHomogeneous (norm : V → ℝ) where
  nonneg := norm_nonneg
  eq_zero_iff := fun _ => norm_eq_zero
  smul_nonneg t ht x := by rw [norm_smul, Real.norm_of_nonneg ht]

theorem real_norm_localSphereLipschitz (n : ℕ) : RealLocalSphereLipschitz n (norm : V → ℝ) := by
  intro Y hfinite hY
  letI : FiniteDimensional ℝ Y := hfinite
  let e := LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin (n + 1))) Y (by rw [hY]; simp)
  let f : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] V :=
    LinearMap.toContinuousLinearMap (Y.subtype.comp e.toLinearMap)
  refine ⟨e, ‖f‖₊, ?_⟩
  simpa only [Function.comp_def, one_mul] using (lipschitzWith_one_norm.comp f.lipschitz).lipschitzOnWith

def MetricGeometry.PositiveGaugeData.innerProductSpaceOfNorm
    (D : MetricGeometry.PositiveGaugeData (norm : V → ℝ)) : InnerProductSpace ℝ V where
  __ := inferInstanceAs (NormedSpace ℝ V)
  inner x y := D.bilinear x y
  norm_sq_eq_re_inner x := (D.diagonal x).symm
  conj_inner_symm x y := D.symmetric y x
  add_left x y z := by change D.bilinear (x + y) z = _; rw [D.bilinear.map_add]; rfl
  smul_left x y r := by change D.bilinear (r • x) y = r * D.bilinear x y; rw [D.bilinear.map_smul]; rfl

variable (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
  ∀ j : ℕ, Even (j + 2) →
  ∀ α : HomotopyGroup (Fin (j + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem real_odd_norm_positiveGaugeData_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hdim : (n : Cardinal) < Module.rank ℝ V)
    (hmetric : MetricSubspaceHomogeneity ℝ V n) :
    Nonempty (MetricGeometry.PositiveGaugeData (norm : V → ℝ)) := by
  apply positiveGaugeData_of_real_odd_sections_of_body_even_homotopy_torsion hTorsion
    real_norm_algebraicPositiveHomogeneous hn hodd hdim (real_norm_localSphereLipschitz n)
  intro E F hE hF
  letI : Module.Finite ℝ E := Module.finite_of_finrank_pos (by rw [hE]; omega)
  letI : Module.Finite ℝ F := Module.finite_of_finrank_pos (by rw [hF]; omega)
  obtain ⟨T⟩ := hmetric E F (by rw [← Module.finrank_eq_rank, hE]) (by rw [← Module.finrank_eq_rank, hF])
  let U := T.toRealLinearIsometryEquiv
  exact ⟨U.toLinearEquiv, fun x => U.norm_map x⟩

theorem real_odd_normedCorollaryB_of_body_even_homotopy_torsion
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hdim : (n : Cardinal) < Module.rank ℝ V)
    (hmetric : MetricSubspaceHomogeneity ℝ V n) : HasInnerProductForGivenScalarAction ℝ V := by
  obtain ⟨D⟩ := real_odd_norm_positiveGaugeData_of_body_even_homotopy_torsion hTorsion hn hodd hdim hmetric
  exact ⟨D.innerProductSpaceOfNorm, rfl⟩

end
end BanachIsometric

