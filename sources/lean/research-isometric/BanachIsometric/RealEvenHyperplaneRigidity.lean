import BanachIsometric.EvenAmbientSectionRigidity
import BanachIsometric.RealOddHyperplaneTorsion

/-! Real even-dimensional central sections give an actual ambient positive
quadratic form. This is the Gromov branch, proved using actual hemisphere
clutching, covariance normalization, sphere transitivity and the constructed
hairy-ball obstruction. No external Gromov or homotopy-torsion premise remains. -/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

noncomputable section

theorem real_even_hyperplane_quadratic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (k : ℕ) (hdim : Module.finrank ℝ V = 2 * k + 3) {p : V → ℝ}
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : V) 1))
    (hSections : RealEquivalentRealSections (2 * k + 2) p) :
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
  have hrank (a : sphere (0 : V) 1) : Module.finrank ℝ (normalHyperplane a) = 2 * k + 2 :=
    normalHyperplane_finrank (by omega) a
  have hEquivalent (a : sphere (0 : V) 1) :
      RealSectionEquivalent p (normalHyperplane v) (normalHyperplane a) := by
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
  obtain ⟨a, hva, _hva'⟩ := hpair v.val v.val
  have horth : inner ℝ v.val a.val = 0 :=
    (real_inner_comm _ _).trans (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hva)
  let q₀ : EquatorSphere v := ⟨⟨a.val,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr horth⟩, by
    rw [mem_sphere, dist_zero_right]
    exact norm_eq_of_mem_sphere a⟩
  letI : NeZero (2 * k + 2) := ⟨by omega⟩
  obtain ⟨w₀, hw₀⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin (2 * k + 2)))
    (by norm_num : (0 : ℝ) ≤ 1)
  let w : sphere (0 : EuclideanSpace ℝ (Fin (2 * k + 2))) 1 :=
    ⟨w₀, by simpa only [mem_sphere, dist_zero_right] using hw₀⟩
  letI : NeZero (Module.finrank ℝ V) := ⟨by omega⟩
  let e : V ≃L[ℝ] PiolaSpace (Module.finrank ℝ V) :=
    (stdOrthonormalBasis ℝ V).repr.toContinuousLinearEquiv |>.trans
      (euclideanCoordinates (Module.finrank ℝ V))
  have hOdd : Odd (Module.finrank ℝ V) := by rw [hdim]; exact ⟨k + 1, by omega⟩
  obtain ⟨Q, hQpos, hQ, _hbody⟩ := D.exists_ambient_quadraticForm_of_odd_ambient_rank
    volume hp hSphere lipschitzWith_normalHyperplane_projection.continuous (fun _ => le_rfl)
    e hOdd v q₀ w hpair
  exact ⟨Q, hQpos, hQ⟩

end
end BanachIsometric
