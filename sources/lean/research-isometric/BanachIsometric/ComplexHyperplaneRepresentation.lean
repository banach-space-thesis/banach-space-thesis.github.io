import BanachIsometric.ComplexHyperplaneField

/-!
# Unit normals represent the genuine complex hyperplanes

The sphere parameterization used by the exact-section bundle covers every
complex hyperplane. Coordinates below are actual real linear isometries;
they do not install a replacement complex action on real coordinate space.
-/

namespace BanachIsometric

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

theorem exists_unit_normal_eq_complexNormalHyperplane {n : ℕ}
    (hdim : Module.finrank ℂ V = n + 1) (K : Submodule ℂ V)
    (hK : Module.finrank ℂ K = n) :
    ∃ u : V, ‖u‖ = 1 ∧ complexNormalHyperplane u = K := by
  have horth : Module.finrank ℂ Kᗮ = 1 := by
    have h := K.finrank_add_finrank_orthogonal
    omega
  let b : OrthonormalBasis (Fin 1) ℂ Kᗮ :=
    (stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr horth)
  let u : V := (b 0 : V)
  have hu : ‖u‖ = 1 := b.orthonormal.1 0
  refine ⟨u, hu, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    exact Submodule.inner_left_of_mem_orthogonal hx (b 0).property
  · have h := complexNormalHyperplane_finrank_add_one u hu
    omega

theorem complexNormalHyperplane_finrank (n : ℕ)
    (u : Metric.sphere (0 : ComplexHermitianAmbient n) 1) :
    Module.finrank ℂ (complexNormalHyperplane u.val) = n := by
  have hu : ‖u.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  have h := complexNormalHyperplane_finrank_add_one u.val hu
  have hdim : Module.finrank ℂ (ComplexHermitianAmbient n) = n + 1 :=
    finrank_euclideanSpace_fin
  rw [hdim] at h
  exact Nat.add_right_cancel h

theorem exists_complexHyperplaneField_eq (n : ℕ)
    (K : Submodule ℂ (ComplexHermitianAmbient n)) (hK : Module.finrank ℂ K = n) :
    ∃ u : Metric.sphere (0 : ComplexHermitianAmbient n) 1,
      complexNormalHyperplane u.val = K ∧ complexHyperplaneField n u = K.restrictScalars ℝ := by
  obtain ⟨u, hu, heq⟩ := exists_unit_normal_eq_complexNormalHyperplane
    (by simp [ComplexHermitianAmbient]) K hK
  refine ⟨⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩, heq, ?_⟩
  exact congrArg (Submodule.restrictScalars ℝ) heq

theorem complexHermitianAmbient_real_finrank (n : ℕ) :
    Module.finrank ℝ (ComplexHermitianAmbient n) = 2 * (n + 1) := by
  have h := Module.finrank_mul_finrank ℝ ℂ (ComplexHermitianAmbient n)
  simpa only [Complex.finrank_real_complex, ComplexHermitianAmbient,
    finrank_euclideanSpace_fin] using h.symm

/-- Coordinates for the existing real Euclidean restriction. The choice of
orthonormal basis is immaterial; the norm and real action are preserved. -/
def complexHermitianAmbient_realCoordinates (n : ℕ) :
    EuclideanSpace ℝ (Fin (2 * (n + 1))) ≃ₗᵢ[ℝ] ComplexHermitianAmbient n :=
  ((stdOrthonormalBasis ℝ (ComplexHermitianAmbient n)).reindex
    (finCongr (complexHermitianAmbient_real_finrank n))).repr.symm

end

end BanachIsometric
