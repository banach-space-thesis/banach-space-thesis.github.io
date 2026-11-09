import BanachIsometric.ExactFamilyGeneralTheorem

/-! The paper's full exact-family statement on the original spaces, with
the literal star body and a merely continuous nonzero-degree normal map. -/

namespace BanachIsometric

open scoped NNReal

theorem exactFamilyTheorem3_1_original_spaces
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [Nontrivial V] [NeZero (Module.finrank ℝ V)]
    (K : RadialStarBody V) {p : E → ℝ} (hp : IsDefinitePositiveHomogeneous p)
    {C : ℝ≥0} (hK : LipschitzWith C K.radius)
    (A : ExactTangentialFamily E V K.gauge p)
    (e : V ≃L[ℝ] PiolaSpace (Module.finrank ℝ V))
    (hEven : Even (Module.finrank ℝ V)) (hdegree : A.continuousNormalDegree e ≠ 0) :
    (∃ c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      ∀ k : ℕ, ∃ P : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ,
        P.IsHomogeneous (Module.finrank ℝ V + 2 * k) ∧
        ∀ y : E, MvPolynomial.eval (fun j => c y j) P = p y ^ (Module.finrank ℝ V + 2 * k)) ∧
    ∃ Q : QuadraticForm ℝ E, Q.PosDef ∧ ∀ y, Q y = p y ^ 2 := by
  obtain ⟨L, hL⟩ := K.exists_gauge_lipschitz hK
  exact A.exactFamilyRigidity_original_spaces e hp K.gauge_homogeneous hL.continuous hEven hdegree

end BanachIsometric
