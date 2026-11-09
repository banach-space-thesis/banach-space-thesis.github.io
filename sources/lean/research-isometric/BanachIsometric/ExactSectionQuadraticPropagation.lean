import BanachIsometric.NonzeroPullbackRigidity
import BanachIsometric.ContinuousDegreeFieldRigidity

/-!
# Propagating the reference ellipsoid through the original exact atlas

Once the reference square is quadratic, the original exact section
equivalences transfer its quadratic identities to every section. Pair
coverage and continuity reconstruct the ambient quadratic form. This uses
the original equivalences directly, instead of using surjectivity of the
nonzero-degree normal map for this last propagation step.
-/

namespace BanachIsometric

open Set Metric MeasureTheory
open scoped Topology NNReal

theorem exists_posDef_quadraticForm_of_pairwise_exact_models
    {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} (hg : IsDefinitePositiveHomogeneous g) (hcont : Continuous g)
    (Q : QuadraticForm ℝ E) (T : I → E →L[ℝ] F)
    (hdiag : ∀ i y, Q y = g (T i y) ^ 2)
    (hpair : ∀ x y : F, ∃ i, x ∈ Set.range (T i) ∧ y ∈ Set.range (T i)) :
    ∃ R : QuadraticForm ℝ F, R.PosDef ∧ ∀ x, R x = g x ^ 2 := by
  have hsmul (a : ℝ) (x : F) : g (a • x) ^ 2 = a ^ 2 * g x ^ 2 := by
    obtain ⟨i, ⟨u, rfl⟩, _⟩ := hpair x 0
    rw [← map_smul, ← hdiag, ← hdiag, Q.map_smul]
    simp only [smul_eq_mul, pow_two]
  have hpara (x y : F) : g (x + y) ^ 2 + g (x - y) ^ 2 = 2 * (g x ^ 2 + g y ^ 2) := by
    obtain ⟨i, ⟨u, rfl⟩, ⟨v, rfl⟩⟩ := hpair x y
    rw [← map_add, ← map_sub, ← hdiag, ← hdiag, ← hdiag, ← hdiag]
    exact quadraticForm_parallelogram Q u v
  obtain ⟨R, hR⟩ := exists_quadraticForm_of_continuous_parallelogram
    (fun x => g x ^ 2) (hcont.pow 2) (by
      change g 0 ^ 2 = 0
      rw [(hg.eq_zero_iff 0).mpr rfl]
      norm_num) hsmul hpara
  refine ⟨R, fun x hx => ?_, hR⟩
  rw [hR]
  exact sq_pos_iff.mpr ((hg.eq_zero_iff x).not.mpr hx)

namespace ExactSectionPrincipalData

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F}
  {a₀ : sphere (0 : F) 1}

omit [FiniteDimensional ℝ F] in
theorem exists_ambient_quadraticForm_of_reference_quadraticForm
    (D : ExactSectionPrincipalData m p H a₀)
    (hp : IsDefinitePositiveHomogeneous p) (hcont : Continuous p)
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)))
    (hQ : ∀ y, Q y = p (D.reference y) ^ 2)
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ R : QuadraticForm ℝ F, R.PosDef ∧ (∀ x, R x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | R x ≤ 1} := by
  let T := fun a => D.atlas.forward a a
  have hvalid (a) := D.atlas.forward_valid a a (D.atlas.mem_baseSet a)
  have hRange (a) : Set.range (T a) = (H a : Set F) := by
    change (LinearMap.range (T a).toLinearMap : Set F) = (H a : Set F)
    rw [(hvalid a).2.1]
  have hGauge (a) : ∀ y, p (T a y) = p (D.reference y) := by
    apply gauge_eq_of_exact_body_image (hp.comp_linearIsometry D.reference) hp
      (T a).toLinearMap (hvalid a).1
    change T a '' D.ModelBody = {x | p x ≤ 1} ∩ Set.range (T a)
    rw [hRange]
    exact (hvalid a).2.2
  have hdiag (a) (y) : Q y = p (T a y) ^ 2 := by rw [hQ, hGauge]
  have hpairs : ∀ x y, ∃ a, x ∈ Set.range (T a) ∧ y ∈ Set.range (T a) := by
    intro x y
    obtain ⟨a, hx, hy⟩ := hpair x y
    exact ⟨a, by rwa [hRange], by rwa [hRange]⟩
  obtain ⟨R, hRpos, hR⟩ := exists_posDef_quadraticForm_of_pairwise_exact_models hp hcont Q T hdiag hpairs
  exact ⟨R, hRpos, hR, gauge_sublevel_eq_quadratic_sublevel hp.nonneg R hR⟩

omit [FiniteDimensional ℝ F] in
theorem exists_section_quadraticForm_of_reference_quadraticForm
    (D : ExactSectionPrincipalData m p H a₀) (hp : IsDefinitePositiveHomogeneous p)
    (Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)))
    (hQ : ∀ y, Q y = p (D.reference y) ^ 2) (a : sphere (0 : F) 1) :
    ∃ R : QuadraticForm ℝ (H a), R.PosDef ∧ (∀ y, R y = p y.val ^ 2) ∧
      {y : H a | p y.val ≤ 1} = {y | R y ≤ 1} := by
  have hvalid := D.atlas.forward_valid a a (D.atlas.mem_baseSet a)
  have hRange : Set.range (D.atlas.forward a a) = (H a : Set F) := by
    change (LinearMap.range (D.atlas.forward a a).toLinearMap : Set F) = (H a : Set F)
    rw [hvalid.2.1]
  have hGauge : ∀ y, p (D.atlas.forward a a y) = p (D.reference y) := by
    apply gauge_eq_of_exact_body_image (hp.comp_linearIsometry D.reference) hp
      (D.atlas.forward a a).toLinearMap hvalid.1
    change D.atlas.forward a a '' D.ModelBody = {x | p x ≤ 1} ∩ Set.range (D.atlas.forward a a)
    rw [hRange]
    exact hvalid.2.2
  let R : QuadraticForm ℝ (H a) := Q.comp
    ((D.atlas.inverse a a).toLinearMap.comp (H a).subtype)
  have hR (y : H a) : R y = p y.val ^ 2 := by
    change Q (D.atlas.inverse a a y.val) = p y.val ^ 2
    rw [hQ]
    have hgauge := hGauge (D.atlas.inverse a a y.val)
    rw [D.atlas.forward_inverse_apply a a (D.atlas.mem_baseSet a) y.val y.property] at hgauge
    exact congrArg (fun r : ℝ => r ^ 2) hgauge.symm
  refine ⟨R, ?_, hR, gauge_sublevel_eq_quadratic_sublevel (fun y => hp.nonneg y.val) R hR⟩
  intro y hy
  rw [hR]
  apply sq_pos_iff.mpr
  intro hz
  apply hy
  apply Subtype.ext
  exact (hp.eq_zero_iff y.val).mp hz

theorem exists_ambient_quadraticForm_of_nonzero_pullback_section
    [NeZero (Module.finrank ℝ F)] (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (φ : C(sphere (0 : F) 1, sphere (0 : F) 1))
    (B : C(sphere (0 : F) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hB : ∀ a, Function.Injective (B a) ∧ LinearMap.range (B a).toLinearMap = H (φ a) ∧
      B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (φ a) : Set F))
    (e : F ≃L[ℝ] PiolaSpace (Module.finrank ℝ F)) (hEven : Even (Module.finrank ℝ F))
    (hdegree : continuousSphereSignedDegree e φ ≠ 0)
    (hpair : ∀ x y, ∃ a, x ∈ H a ∧ y ∈ H a) :
    ∃ R : QuadraticForm ℝ F, R.PosDef ∧ (∀ x, R x = p x ^ 2) ∧
      {x | p x ≤ 1} = {x | R x ≤ 1} := by
  obtain ⟨Q, _hQpos, hQ⟩ := D.exists_reference_quadraticForm_of_nonzero_pullback_section
    μ hp hSphere hProj hTangent φ B hB e hEven hdegree
  obtain ⟨L, hL⟩ := hp.exists_lipschitzWith hSphere
  exact D.exists_ambient_quadraticForm_of_reference_quadraticForm hp hL.continuous Q hQ hpair

end ExactSectionPrincipalData
end BanachIsometric
