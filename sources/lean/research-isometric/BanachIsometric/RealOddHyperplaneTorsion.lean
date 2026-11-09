import BanachIsometric.ExactSectionFiniteOrderRigidity
import BanachIsometric.RealHyperplaneBundle
import BanachIsometric.HyperplanePairCoverage

/-! The actual full real hyperplane field in even ambient dimension at least
four supplies the odd-section geometric rigidity argument. All projection,
rank, tangency and pair-coverage premises are derived. Only the actual compact
body even-homotopy torsion theorem remains an explicit external premise. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology Topology.Homotopy NNReal

noncomputable section

def RealEquivalentRealSections {X : Type*} [AddCommGroup X] [Module ℝ X]
    (n : ℕ) (p : X → ℝ) : Prop :=
  ∀ E F : Submodule ℝ X, Module.finrank ℝ E = n → Module.finrank ℝ F = n →
    ∃ T : E ≃ₗ[ℝ] F, ∀ x : E, p (T x : X) = p (x : X)

variable (hTorsion : ∀ (d : ℕ) (S : Set (EuclideanSpace ℝ (Fin d))),
  IsCompact S → closure (interior S) = S → (0 : EuclideanSpace ℝ (Fin d)) ∈ interior S →
  ∀ j : ℕ, Even (j + 2) →
  ∀ α : HomotopyGroup (Fin (j + 2))
    (Subgroup.connectedComponentOfOne (bodyAutomorphismGroup S)) 1, IsOfFinOrder α)

include hTorsion

theorem real_odd_hyperplane_quadratic_of_body_even_homotopy_torsion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (k : ℕ) (hdim : Module.finrank ℝ V = 2 * k + 4) {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : V) 1))
    (hSections : RealEquivalentRealSections (2 * k + 3) p) :
    ∃ Q : QuadraticForm ℝ V, Q.PosDef ∧ ∀ x, Q x = p x ^ 2 := by
  have hpair : ∀ x y : V, ∃ a : sphere (0 : V) 1,
      x ∈ normalHyperplane a ∧ y ∈ normalHyperplane a := by
    intro x y
    obtain ⟨u, hu, hux, huy⟩ := exists_unit_normal_annihilating_pair (𝕜 := ℝ)
      (by rw [hdim]; omega) x y
    let a : sphere (0 : V) 1 := ⟨u, by simpa only [mem_sphere, dist_zero_right] using hu⟩
    exact ⟨a, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hux,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huy⟩
  obtain ⟨v, _hv₁, _hv₂⟩ := hpair 0 0
  have hrank (a : sphere (0 : V) 1) : Module.finrank ℝ (normalHyperplane a) = 2 * k + 3 :=
    normalHyperplane_finrank (by omega) a
  have hEquivalent (a : sphere (0 : V) 1) : RealSectionEquivalent p (normalHyperplane v) (normalHyperplane a) := by
    obtain ⟨T, hT⟩ := hSections _ _ (hrank v) (hrank a)
    refine ⟨T, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change p (T x : V) ≤ 1
      rw [hT]
      exact hx
    · intro hy
      refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
      change p (T.symm y : V) ≤ 1
      rw [← hT, T.apply_symm_apply]
      exact hy
  obtain ⟨D⟩ := nonempty_exactSectionPrincipalData volume hp hSphere normalHyperplane
    lipschitzWith_normalHyperplane_projection
    (fun a => by simpa only [finrank_euclideanSpace_fin] using hrank a) v hEquivalent
  obtain ⟨hS, hreg, h0⟩ := D.modelBody_geometric_properties hp hSphere
  have hEven : Even (Module.finrank ℝ V) := by rw [hdim]; exact ⟨k + 2, by omega⟩
  have hIndexEven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  have hTor : ∀ α : HomotopyGroup (Fin ((2 * k + 1) + 1))
      (Subgroup.connectedComponentOfOne D.StructureGroup) 1, IsOfFinOrder α :=
    hTorsion (2 * k + 3) D.ModelBody hS hreg h0 (2 * k) hIndexEven
  let e : V ≃L[ℝ] PiolaSpace (Module.finrank ℝ V) :=
    (stdOrthonormalBasis ℝ V).repr.toContinuousLinearEquiv |>.trans
      (euclideanCoordinates (Module.finrank ℝ V))
  obtain ⟨Q, hQpos, hQ, _hbody⟩ := D.exists_ambient_quadraticForm_of_actual_homotopy_torsion
    volume hp hSphere lipschitzWith_normalHyperplane_projection (fun _ => le_rfl)
    v (2 * k + 1) (by omega) hEven hTor e hpair
  exact ⟨Q, hQpos, hQ⟩

end
end BanachIsometric
