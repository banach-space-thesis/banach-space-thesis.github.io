import BanachIsometric.GenericUnitaryOrbit
import BanachIsometric.TensorGroupAction
import BanachIsometric.InfinitesimalStabilizer

/-!
# Local Lipschitz representatives for the actual finite moment orbit

The general exponential slice theorem is instantiated with the concrete
polynomial tensor representation, whose continuity and smoothness have been
proved. Equal images of a finite body-moment tuple give equal images of the
actual body, by its already proved finite stabilizer theorem.
-/

namespace BanachIsometric

open Filter Set
open scoped Topology NNReal Matrix.Norms.Operator

/-- The actual finite tuple representation has a local Lipschitz lift into
the real orthogonal group, normalized to the identity at its base vector. -/
theorem exists_lipschitz_tensorTuple_orbit_section (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    ∃ s : TensorTupleCoordinates m I → Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ N ∈ 𝓝 M, ∃ L : ℝ≥0,
        s M = 1 ∧ LipschitzOnWith L s N ∧
        ∀ y ∈ N,
          (∃ R : Matrix.orthogonalGroup (Fin m) ℝ,
            tensorTupleLinearRepresentation m I R.val M = y) →
          tensorTupleLinearRepresentation m I (s y).val M = y := by
  letI : CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := compactSpace_orthogonalGroup m
  exact exists_lipschitz_unitary_orbit_section (tensorTupleLinearRepresentation m I)
    (continuous_tensorTupleLinearRepresentation m I) M (contDiff_tensorTupleOrbit m I M)

/-- A finite tuple with the body-stabilizer property detects equality of any
two orthogonal images of the body, not merely equality at the base body. -/
theorem body_images_eq_of_bodyTensorTuple_images_eq {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) (S : Set (Fin m → ℝ))
    (I : Finset ℕ+)
    (hI : ∀ e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ),
      e '' S = S ↔ tensorTupleLinearRepresentation m I
        (LinearMap.toMatrix' e.toLinearMap) (bodyTensorTuple μ S I) = bodyTensorTuple μ S I)
    (Q R : Matrix.orthogonalGroup (Fin m) ℝ)
    (hQR : tensorTupleLinearRepresentation m I R.val (bodyTensorTuple μ S I) =
      tensorTupleLinearRepresentation m I Q.val (bodyTensorTuple μ S I)) :
    R.val.mulVec '' S = Q.val.mulVec '' S := by
  let ρ := tensorTupleLinearRepresentation m I
  let M := bodyTensorTuple μ S I
  let P : Matrix.orthogonalGroup (Fin m) ℝ := Q⁻¹ * R
  have hfix : ρ P.val M = M := by
    change ρ ((Q⁻¹).val * R.val) M = M
    rw [map_mul]
    change ρ (Q⁻¹).val (ρ R.val M) = M
    rw [hQR]
    change ρ (Q⁻¹).val (ρ Q.val M) = M
    rw [← Module.End.mul_apply, ← map_mul]
    have hmul : (Q⁻¹).val * Q.val = 1 := congrArg Subtype.val (inv_mul_cancel Q)
    rw [hmul, map_one]
    rfl
  let e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := Matrix.UnitaryGroup.toLinearEquiv P
  have hmat : LinearMap.toMatrix' e.toLinearMap = P.val :=
    LinearMap.toMatrix'_toLin' P.val
  have he : P.val.mulVec '' S = S := by
    apply (hI e).mpr
    simpa only [hmat] using hfix
  have himg := congrArg (Set.image Q.val.mulVec) he
  rw [Set.image_image] at himg
  have hfun : (fun x => Q.val.mulVec (P.val.mulVec x)) = R.val.mulVec := by
    funext x
    rw [Matrix.mulVec_mulVec]
    have hmul : Q.val * P.val = R.val := by
      exact congrArg Subtype.val (show Q * P = R by simp [P])
    rw [hmul]
  rw [hfun] at himg
  exact himg

/-- The selected tuple of the actual orthogonal image is exactly its image
under the tensor representation. -/
theorem bodyTensorTuple_image_orthogonal {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S) (h0 : μ S ≠ 0)
    (I : Finset ℕ+) (Q : Matrix.orthogonalGroup (Fin m) ℝ) :
    bodyTensorTuple μ (Q.val.mulVec '' S) I =
      tensorTupleLinearRepresentation m I Q.val (bodyTensorTuple μ S I) := by
  let e : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
    (Matrix.UnitaryGroup.toLinearEquiv Q).toContinuousLinearEquiv
  have hmat : LinearMap.toMatrix' e.toLinearMap = Q.val :=
    LinearMap.toMatrix'_toLin' Q.val
  funext ij
  obtain ⟨d, out⟩ := ij
  rw [tensorTupleLinearRepresentation_apply]
  have h := congrFun (bodyTensorMoment_image μ S hS h0 e (r := (d.val : ℕ))) out
  simpa only [hmat, bodyTensorTuple, tensorTupleVector] using h

/-- The local section consequence of Lemma 2.1(iii) needed in Proposition 4.2,
proved directly by exponential coordinates. This is an alternative route to
introducing the quotient's smooth manifold structure. Its values carry the
original body to the specified orthogonal image. -/
theorem exists_lipschitz_bodyMoment_orbit_section {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+,
      ∃ s : TensorTupleCoordinates m I → Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ N ∈ 𝓝 (bodyTensorTuple μ S I), ∃ L : ℝ≥0,
        s (bodyTensorTuple μ S I) = 1 ∧ LipschitzOnWith L s N ∧
        ∀ Q : Matrix.orthogonalGroup (Fin m) ℝ,
          tensorTupleLinearRepresentation m I Q.val (bodyTensorTuple μ S I) ∈ N →
          (s (tensorTupleLinearRepresentation m I Q.val (bodyTensorTuple μ S I))).val.mulVec '' S =
            Q.val.mulVec '' S := by
  obtain ⟨I, hI⟩ := exists_finset_bodyTensorTuple_stabilizer μ S hS hreg h0
  obtain ⟨s, N, hN, L, hs, hLip, hLift⟩ :=
    exists_lipschitz_tensorTuple_orbit_section m I (bodyTensorTuple μ S I)
  refine ⟨I, s, N, hN, L, hs, hLip, ?_⟩
  intro Q hQ
  apply body_images_eq_of_bodyTensorTuple_images_eq μ S I hI Q
  exact hLift _ hQ ⟨Q, rfl⟩

/-- A local Lipschitz rule selects an exact orthogonal map for any body in
the orbit whose actual moment tuple is sufficiently near the reference tuple.
This formulation is ready to compose with a Lipschitz field of body moments.
-/
theorem exists_lipschitz_bodyMoment_image_section {m : ℕ}
    (μ : MeasureTheory.Measure (Fin m → ℝ)) [μ.IsAddHaarMeasure]
    (S : Set (Fin m → ℝ)) (hS : IsCompact S)
    (hreg : closure (interior S) = S) (h0 : μ S ≠ 0) :
    ∃ I : Finset ℕ+,
      ∃ s : TensorTupleCoordinates m I → Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ N ∈ 𝓝 (bodyTensorTuple μ S I), ∃ L : ℝ≥0,
        s (bodyTensorTuple μ S I) = 1 ∧ LipschitzOnWith L s N ∧
        ∀ T : Set (Fin m → ℝ),
          (∃ Q : Matrix.orthogonalGroup (Fin m) ℝ, Q.val.mulVec '' S = T) →
          bodyTensorTuple μ T I ∈ N → (s (bodyTensorTuple μ T I)).val.mulVec '' S = T := by
  obtain ⟨I, s, N, hN, L, hs, hLip, hLift⟩ :=
    exists_lipschitz_bodyMoment_orbit_section μ S hS hreg h0
  refine ⟨I, s, N, hN, L, hs, hLip, ?_⟩
  intro T ⟨Q, hQ⟩ hT
  rw [← hQ] at hT ⊢
  rw [bodyTensorTuple_image_orthogonal μ S hS h0 I Q] at hT ⊢
  exact hLift Q hT

end BanachIsometric
