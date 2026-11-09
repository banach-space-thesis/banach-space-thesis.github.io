import BanachIsometric.GrassmannianProjectionSmooth
import BanachIsometric.SphericalSectionsTorsion

/-!
# Spherical sections for an actual smooth Grassmannian field

This is the graph-chart Grassmannian version of the paper's spherical-sections
statement. The canonical projector criterion is derived from the genuine
manifold smoothness predicate. The remaining compact-body-group even-homotopy
torsion input is explicit. The body and its original real sections are retained.
-/

noncomputable section
namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal Manifold

theorem RadialStarBody.spherical_sections_quadratic_of_smooth_grassmannian_field
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V] (K : RadialStarBody V) {C : ℝ≥0} (hK : LipschitzWith C K.radius)
    (k : ℕ) (hdim : Module.finrank ℝ V = 2 * k + 4) (m : ℕ)
    (H : sphere (0 : V) 1 → RealGrassmannian V m)
    (hSmooth : letI : Fact (Module.finrank ℝ V = (2 * k + 3) + 1) := ⟨hdim⟩
      letI := realGrassmannianChartedSpace V m
      ContMDiff (𝓡 (2 * k + 3)) (modelWithCornersSelf ℝ (GrassmannianModel V m)) (⊤ : ℕ∞) H)
    (hTangent : ∀ a, (H a).val ≤ normalHyperplane a)
    (v : sphere (0 : V) 1)
    (hEquivalent : ∀ a, RealSectionEquivalent K.gauge (H v).val (H a).val)
    (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
      IsCompact S → closure (interior S) = S →
      (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
      ∀ j : ℕ, Even (j + 2) →
      ∀ α : HomotopyGroup (Fin (j + 2))
        (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α) :
    (∀ a, ∃ Q : QuadraticForm ℝ (H a).val, Q.PosDef ∧
      (∀ y, Q y = K.gauge y.val ^ 2) ∧
      {y : (H a).val | y.val ∈ K.carrier} = {y | Q y ≤ 1}) ∧
    ((∀ x y : V, ∃ a, x ∈ (H a).val ∧ y ∈ (H a).val) →
      ∃ Q : QuadraticForm ℝ V, Q.PosDef ∧ (∀ x, Q x = K.gauge x ^ 2) ∧
        K.carrier = {x | Q x ≤ 1}) := by
  letI : Fact (Module.finrank ℝ V = (2 * k + 3) + 1) := ⟨hdim⟩
  letI := realGrassmannianChartedSpace V m
  have hProjection : ContMDiff (𝓡 (2 * k + 3)) (modelWithCornersSelf ℝ (V →L[ℝ] V)) 1
      (fun a => (H a).val.starProjection) :=
    ((contMDiff_realGrassmannian_iff_projection H).mp hSmooth).of_le (by norm_num)
  exact K.spherical_sections_quadratic_of_body_even_homotopy_torsion hK k hdim
    (fun a => (H a).val) hProjection hTangent m (fun a => (H a).property)
    v hEquivalent hTorsion

end BanachIsometric
