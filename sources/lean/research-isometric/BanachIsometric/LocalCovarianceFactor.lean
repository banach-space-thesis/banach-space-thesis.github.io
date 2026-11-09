import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Topology.Algebra.Star
import Mathlib.Analysis.Normed.Ring.Units

/-!
# A local Lipschitz covariance factor by the inverse function theorem

The square map on the entire real Banach algebra has derivative `2 • id` at
`1`. Its local inverse is Lipschitz. For a self-adjoint input, taking the star
produces another nearby square root, so local injectivity makes the root
self-adjoint. This gives the factor needed for covariance normalization,
without assuming any regularity theorem about the global positive square root.
-/

namespace BanachIsometric

open Filter Set
open scoped Topology NNReal

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The derivative of the square map at the identity, bundled as an actual
continuous linear equivalence. The algebra may be noncommutative. -/
def doubleLinearEquiv : A ≃L[ℝ] A :=
  ContinuousLinearEquiv.equivOfInverse
    ((2 : ℝ) • ContinuousLinearMap.id ℝ A)
    (((2 : ℝ)⁻¹) • ContinuousLinearMap.id ℝ A)
    (by intro x; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_smul]; norm_num)
    (by intro x; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_smul]; norm_num)

@[simp]
theorem doubleLinearEquiv_apply (x : A) : doubleLinearEquiv x = (2 : ℝ) • x := rfl

theorem hasStrictFDerivAt_square_one :
    HasStrictFDerivAt (fun x : A ↦ x * x)
      (doubleLinearEquiv (A := A) : A →L[ℝ] A) 1 := by
  have h := (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : A)).fun_mul'
    (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : A))
  convert h using 1
  ext x
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  simp [two_smul]

variable [CompleteSpace A] [StarRing A] [ContinuousStar A]

/-- An actual locally Lipschitz factor near the identity in any real Banach
star algebra with continuous involution. The factor is invertible and
self-adjoint when its input is self-adjoint, and satisfies `B * star B = C`.
No positivity or square-root regularity is assumed. -/
theorem exists_lipschitz_local_covarianceFactor :
    ∃ B : A → A, ∃ U : Set A, ∃ K : ℝ≥0,
      IsOpen U ∧ (1 : A) ∈ U ∧ B 1 = 1 ∧ LipschitzOnWith K B U ∧
      (∀ C ∈ U, IsUnit (B C)) ∧
      (∀ C ∈ U, IsSelfAdjoint C →
        IsSelfAdjoint (B C) ∧ B C * star (B C) = C) := by
  let f : A → A := fun x ↦ x * x
  have hf : HasStrictFDerivAt f (doubleLinearEquiv (A := A) : A →L[ℝ] A) 1 :=
    hasStrictFDerivAt_square_one
  let P := hf.toOpenPartialHomeomorph f
  let B := hf.localInverse f (doubleLinearEquiv (A := A)) 1
  have hf1 : f 1 = 1 := one_mul 1
  have hB1 : B 1 = 1 := by
    simpa only [hf1, B] using hf.localInverse_apply_image
  have hBderiv : HasStrictFDerivAt B
      ((doubleLinearEquiv (A := A)).symm : A →L[ℝ] A) 1 := by
    simpa only [hf1, B] using hf.to_localInverse
  obtain ⟨K, W, hW, hLip⟩ := hBderiv.exists_lipschitzOnWith
  have hB : Tendsto B (𝓝 (1 : A)) (𝓝 (1 : A)) := by
    simpa only [hB1] using hBderiv.continuousAt.tendsto
  have hsource : P.source ∈ 𝓝 (1 : A) :=
    P.open_source.mem_nhds hf.mem_toOpenPartialHomeomorph_source
  have hstar : Tendsto (fun C ↦ star (B C)) (𝓝 (1 : A)) (𝓝 (1 : A)) := by
    simpa only [star_one] using (continuous_star.tendsto (1 : A)).comp hB
  have heq : ∀ᶠ C in 𝓝 (1 : A), B C * B C = C := by
    simpa only [hf1, B, f] using hf.eventually_right_inverse
  have hconditions : ∀ᶠ C in 𝓝 (1 : A), C ∈ W ∧ B C ∈ P.source ∧
      star (B C) ∈ P.source ∧ IsUnit (B C) ∧ B C * B C = C := by
    filter_upwards [hW, hB hsource, hstar hsource, hB (Units.nhds (1 : Aˣ)), heq]
      with C hCW hBC hstarBC hunit hsq
    exact ⟨hCW, hBC, hstarBC, hunit, hsq⟩
  obtain ⟨U, hUsub, hUopen, h1U⟩ := mem_nhds_iff.mp hconditions
  refine ⟨B, U, K, hUopen, h1U, hB1, hLip.mono (fun C hC ↦ (hUsub hC).1),
    fun C hC ↦ (hUsub hC).2.2.2.1, ?_⟩
  intro C hCU hC
  have hBC := (hUsub hCU).2.1
  have hstarBC := (hUsub hCU).2.2.1
  have hsq := (hUsub hCU).2.2.2.2
  have hself : IsSelfAdjoint (B C) := by
    apply isSelfAdjoint_iff.mpr
    apply P.injOn hstarBC hBC
    change star (B C) * star (B C) = B C * B C
    rw [← star_mul, hsq, hC.star_eq]
  exact ⟨hself, by simpa only [hself.star_eq] using hsq⟩

/-- The inverse factor whitens every nearby self-adjoint input, and itself
depends locally Lipschitz-continuously on that input. -/
theorem exists_lipschitz_local_covarianceWhitening :
    ∃ Q : A → A, ∃ U : Set A, ∃ K : ℝ≥0,
      IsOpen U ∧ (1 : A) ∈ U ∧ Q 1 = 1 ∧ LipschitzOnWith K Q U ∧
      (∀ C ∈ U, IsUnit (Q C)) ∧
      (∀ C ∈ U, IsSelfAdjoint C →
        IsSelfAdjoint (Q C) ∧ Q C * C * star (Q C) = 1) := by
  obtain ⟨B, V, KB, hV, h1V, hB1, hBLip, hBunit, hBfac⟩ :=
    exists_lipschitz_local_covarianceFactor (A := A)
  have hBcont : ContinuousAt B (1 : A) := hBLip.continuousOn.continuousAt (hV.mem_nhds h1V)
  have hInv := hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (1 : Aˣ)
  obtain ⟨KI, W, hW, hILip⟩ := hInv.exists_lipschitzOnWith
  have hBW : B ⁻¹' W ∈ 𝓝 (1 : A) :=
    hBcont.preimage_mem_nhds (by simpa only [hB1, Units.val_one] using hW)
  obtain ⟨U, hUsub, hUopen, h1U⟩ := mem_nhds_iff.mp (inter_mem (hV.mem_nhds h1V) hBW)
  let Q : A → A := fun C ↦ Ring.inverse (B C)
  refine ⟨Q, U, KI * KB, hUopen, h1U, ?_, ?_, ?_, ?_⟩
  · simp only [Q, hB1, Ring.inverse_one]
  · exact hILip.comp (hBLip.mono (hUsub.trans inter_subset_left))
      (fun C hC ↦ (hUsub hC).2)
  · intro C hCU
    exact (hBunit C (hUsub hCU).1).ringInverse
  · intro C hCU hC
    obtain ⟨hself, hfac⟩ := hBfac C (hUsub hCU).1 hC
    have hunit := hBunit C (hUsub hCU).1
    refine ⟨?_, ?_⟩
    · change IsSelfAdjoint (Ring.inverse (B C))
      rw [isSelfAdjoint_iff, ← Ring.inverse_star, hself.star_eq]
    · change Ring.inverse (B C) * C * star (Ring.inverse (B C)) = 1
      calc
        Ring.inverse (B C) * C * star (Ring.inverse (B C)) =
            Ring.inverse (B C) * (B C * star (B C)) * star (Ring.inverse (B C)) := by
          rw [hfac]
        _ = 1 := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul,
            ← Ring.inverse_star, Ring.mul_inverse_cancel _ hunit.star]

end

end BanachIsometric
