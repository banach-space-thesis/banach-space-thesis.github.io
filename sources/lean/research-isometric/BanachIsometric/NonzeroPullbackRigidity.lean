import BanachIsometric.PullbackSphereRegularization
import BanachIsometric.ExactTangentialBundleSection
import BanachIsometric.ExactFamilyGeneralTheorem

/-!
# The bundle-to-analytic bridge preserving the actual continuous degree

An actual continuous exact section over an actual sphere pullback is
regularized together with its base map. Its degree is preserved by the
literal constructed homotopy, and its exact body identities give the genuine
tangential family. The second endpoint derives the reference quadratic form.

Existence of the input nonzero-degree pullback section is still a separate
topological obligation. It is not hidden in the bundle data or asserted here.
-/

noncomputable section
namespace BanachIsometric.ExactSectionPrincipalData

open Set Metric MeasureTheory
open scoped Topology NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {m : ℕ} {p : F → ℝ} {H : sphere (0 : F) 1 → Submodule ℝ F}
  {a₀ : sphere (0 : F) 1}

theorem exists_exactFamily_preserving_pullback_degree
    (D : ExactSectionPrincipalData m p H a₀)
    (μ : Measure (EuclideanSpace ℝ (Fin m))) [μ.IsAddHaarMeasure]
    (hp : IsDefinitePositiveHomogeneous p) {C : ℝ≥0}
    (hSphere : LipschitzOnWith C p (sphere (0 : F) 1)) {LP : ℝ≥0}
    (hProj : LipschitzWith LP (fun a => (H a).starProjection))
    (hTangent : ∀ a, H a ≤ normalHyperplane a)
    (φ : C(sphere (0 : F) 1, sphere (0 : F) 1))
    (B : C(sphere (0 : F) 1, EuclideanSpace ℝ (Fin m) →L[ℝ] F))
    (hB : ∀ a, Function.Injective (B a) ∧ LinearMap.range (B a).toLinearMap = H (φ a) ∧
      B a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (φ a) : Set F))
    {n : ℕ} [NeZero n] (e : F ≃L[ℝ] PiolaSpace n) :
    ∃ A : ExactTangentialFamily (EuclideanSpace ℝ (Fin m)) F p (fun x => p (D.reference x)),
      A.continuousNormalDegree e = continuousSphereSignedDegree e φ ∧
      (∃ L : ℝ≥0, LipschitzWith L A.normal) ∧
      ∀ a, Function.Injective (A.maps a) ∧
        LinearMap.range (A.maps a).toLinearMap = H (A.normal a) ∧
        A.maps a '' D.ModelBody = {y : F | p y ≤ 1} ∩ (H (A.normal a) : Set F) := by
  obtain ⟨ψ, Lψ, T, LT, hψ, hT, ⟨hom⟩, hvalid⟩ :=
    D.exists_lipschitz_sphere_pullback_section_of_continuous μ hp hSphere hProj φ B hB
  have hTangency : ∀ a y, inner ℝ (T a y) (ψ a).val = 0 := by
    intro a y
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    exact hTangent (ψ a) ((hvalid a).2.1.le (LinearMap.mem_range_self (T a).toLinearMap y))
  have hRange (a) : Set.range (T a) = (H (ψ a) : Set F) := by
    change (LinearMap.range (T a).toLinearMap : Set F) = (H (ψ a) : Set F)
    rw [(hvalid a).2.1]
  have hBody (a) : T a '' {x | p (D.reference x) ≤ 1} =
      {y : F | p y ≤ 1} ∩ Set.range (T a) := by
    rw [hRange]
    exact (hvalid a).2.2
  let A := exactTangentialFamilyOfBodyMaps (hp.comp_linearIsometry D.reference) hp ψ T
    ⟨LT, hT⟩ (fun a => (hvalid a).1) hTangency hBody
  refine ⟨A, ?_, ⟨Lψ, hψ⟩, hvalid⟩
  exact (continuousSphereSignedDegree_eq_of_homotopy e hom).symm

theorem exists_reference_quadraticForm_of_nonzero_pullback_section
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
    (hdegree : continuousSphereSignedDegree e φ ≠ 0) :
    ∃ Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m)), Q.PosDef ∧
      ∀ y, Q y = p (D.reference y) ^ 2 := by
  obtain ⟨A, hdegreeA, _hnormal, _hvalid⟩ :=
    D.exists_exactFamily_preserving_pullback_degree μ hp hSphere hProj hTangent φ B hB e
  obtain ⟨L, hL⟩ := hp.exists_lipschitzWith hSphere
  have hnonzero : A.continuousNormalDegree e ≠ 0 := by rwa [hdegreeA]
  exact (A.exactFamilyRigidity_original_spaces e (hp.comp_linearIsometry D.reference)
    hp hL.continuous hEven hnonzero).2

end BanachIsometric.ExactSectionPrincipalData
