import BanachIsometric.MatrixPolar

/-!
# An actual ambient Lipschitz retraction onto a moment stabilizer

The left-orthogonal-equivariant polar correction is composed with the actual
Lipschitz orbit-section correction. This produces an equivariant retraction
from an open matrix neighbourhood of the genuine stabilizer, without tubular
neighbourhood or nearest-point hypotheses.
-/

namespace BanachIsometric

open Set Filter
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

def tensorStarOrbit (m : ℕ) (I : Finset ℕ+) (M : TensorTupleCoordinates m I)
    (T : Matrix (Fin m) (Fin m) ℝ) : TensorTupleCoordinates m I :=
  tensorTupleLinearRepresentation m I (star T) M

theorem tensorStarOrbit_orthogonal (m : ℕ) (I : Finset ℕ+) (M : TensorTupleCoordinates m I)
    (Q : Matrix.orthogonalGroup (Fin m) ℝ) :
    tensorStarOrbit m I M Q.val = tensorInverseOrbit m I M Q := by
  simp only [tensorStarOrbit, tensorInverseOrbit, tensorTupleOrthogonal_smul_def,
    Matrix.UnitaryGroup.inv_val]

theorem tensorStarOrbit_left_stabilizer (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) (h : Matrix.orthogonalGroup (Fin m) ℝ)
    (hh : h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M)
    (T : Matrix (Fin m) (Fin m) ℝ) :
    tensorStarOrbit m I M (h.val * T) = tensorStarOrbit m I M T := by
  have hinv : h⁻¹ • M = M := (MulAction.mem_stabilizer_iff).mp
    ((MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M).inv_mem hh)
  have hf : tensorTupleLinearRepresentation m I (star h.val) M = M := by
    simpa only [tensorTupleOrthogonal_smul_def, Matrix.UnitaryGroup.inv_val] using hinv
  unfold tensorStarOrbit
  rw [star_mul, map_mul]
  change tensorTupleLinearRepresentation m I (star T)
    (tensorTupleLinearRepresentation m I (star h.val) M) = _
  rw [hf]

theorem exists_ambient_lipschitz_tensor_stabilizer_retraction (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    ∃ U : Set (Matrix (Fin m) (Fin m) ℝ),
      ∃ r : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ, ∃ L : ℝ≥0,
      IsOpen U ∧ LipschitzOnWith L r U ∧
      (∀ h : Matrix.orthogonalGroup (Fin m) ℝ,
        h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M → h.val ∈ U) ∧
      (∀ T ∈ U, r T ∈ unitary (Matrix (Fin m) (Fin m) ℝ) ∧
        tensorTupleLinearRepresentation m I (r T) M = M) ∧
      (∀ h : Matrix.orthogonalGroup (Fin m) ℝ,
        h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M → r h.val = h.val) ∧
      (∀ h : Matrix.orthogonalGroup (Fin m) ℝ,
        h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M →
          ∀ T, r (h.val * T) = h.val * r T) ∧
      (∀ h : Matrix.orthogonalGroup (Fin m) ℝ,
        h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M →
          ∀ T ∈ U, h.val * T ∈ U) := by
  classical
  let O := Matrix.orthogonalGroup (Fin m) ℝ
  letI : CompactSpace O := compactSpace_orthogonalGroup m
  obtain ⟨V, P, KP, hV, hUnitV, hPLip, hPUnit, hPFix, hPEquiv, hPInvariant⟩ :=
    exists_lipschitz_equivariant_matrix_polar m
  obtain ⟨q, N, hN, KQ, hqM, hqLip, hqSect⟩ := exists_lipschitz_tensorTuple_orbit_section m I M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨KC, hcLip⟩ := exists_lipschitz_tensorInverseOrbit m I M
  let f := tensorStarOrbit m I M
  have hOrth (Q : O) : f Q.val = Q⁻¹ • M := tensorStarOrbit_orthogonal m I M Q
  have hLeft (h : O) (hh : h ∈ MulAction.stabilizer O M) (T : Matrix (Fin m) (Fin m) ℝ) :
      f (h.val * T) = f T := tensorStarOrbit_left_stabilizer m I M h hh T
  let U : Set (Matrix (Fin m) (Fin m) ℝ) := V ∩ (fun T => f (P T)) ⁻¹' Metric.ball M ε
  let r : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ := fun T =>
    P T * (q (f (P T))).val
  have hf : Continuous f := (contDiff_tensorTupleOrbit m I M).continuous.comp continuous_star
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro T hT
    have hPV : ContinuousAt P T := hPLip.continuousOn.continuousAt (hV.mem_nhds hT.1)
    have hCP : ContinuousAt (fun A => f (P A)) T := hf.continuousAt.comp (f := P) hPV
    exact inter_mem (hV.mem_nhds hT.1)
      (hCP.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hT.2))
  have hContains : ∀ h : O, h ∈ MulAction.stabilizer O M → h.val ∈ U := by
    intro h hh
    refine ⟨hUnitV h.property, ?_⟩
    have hinv : h⁻¹ • M = M := (MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer O M).inv_mem hh)
    change dist (f (P h.val)) M < ε
    rw [hPFix _ h.property, hOrth h, hinv, dist_self]
    exact hε
  have hCPLip : LipschitzOnWith (KC * KP) (fun T => f (P T)) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro T hT R hR
    let QT : O := ⟨P T, hPUnit T hT.1⟩
    let QR : O := ⟨P R, hPUnit R hR.1⟩
    have hc := hcLip.dist_le_mul QT QR
    rw [← tensorStarOrbit_orthogonal m I M QT, ← tensorStarOrbit_orthogonal m I M QR] at hc
    calc
      dist (f (P T)) (f (P R)) ≤ (KC : ℝ) * dist (P T) (P R) := hc
      _ ≤ (KC : ℝ) * ((KP : ℝ) * dist T R) :=
        mul_le_mul_of_nonneg_left (hPLip.dist_le_mul T hT.1 R hR.1) KC.coe_nonneg
      _ = ((KC * KP : ℝ≥0) : ℝ) * dist T R := by push_cast; ring
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.bddAbove_image
    (continuous_subtype_val : Continuous (fun Q : O => Q.val)).norm.continuousOn
  let B : ℝ≥0 := ⟨max 0 B₀, le_max_left _ _⟩
  have hBound : ∀ Q : O, ‖Q.val‖ ≤ B := fun Q =>
    (hB₀ (mem_image_of_mem (fun R : O => ‖R.val‖) (mem_univ Q))).trans (le_max_right _ _)
  have hQC : LipschitzOnWith (KQ * (KC * KP)) (fun T => (q (f (P T))).val) U :=
    hqLip.comp hCPLip (fun _ h => hball h.2)
  have hrLip : LipschitzOnWith (B * (KQ * (KC * KP)) + KP * B) r U :=
    lipschitzOnWith_ring_mul_of_norm_bounds (hPLip.mono inter_subset_left) hQC
      (fun T hT => hBound ⟨P T, hPUnit T hT.1⟩) (fun T _ => hBound (q (f (P T))))
  refine ⟨U, r, B * (KQ * (KC * KP)) + KP * B, hU, hrLip, hContains, ?_, ?_, ?_, ?_⟩
  · intro T hT
    let Q : O := ⟨P T, hPUnit T hT.1⟩
    have hLift : q (f (P T)) • M = f (P T) :=
      hqSect _ (hball hT.2) ⟨Q⁻¹, (tensorStarOrbit_orthogonal m I M Q).symm⟩
    refine ⟨(unitary _).mul_mem (hPUnit T hT.1) (q (f (P T))).property, ?_⟩
    have hfix : (Q * q (f (P T))) • M = M := by
      rw [mul_smul, hLift]
      change Q • tensorStarOrbit m I M Q.val = M
      rw [tensorStarOrbit_orthogonal]
      exact smul_inv_smul Q M
    exact hfix
  · intro h hh
    have hinv : h⁻¹ • M = M := (MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer O M).inv_mem hh)
    change P h.val * (q (f (P h.val))).val = h.val
    rw [hPFix _ h.property, hOrth h, hinv, hqM]
    exact mul_one _
  · intro h hh T
    change P (h.val * T) * (q (f (P (h.val * T)))).val =
      h.val * (P T * (q (f (P T))).val)
    rw [hPEquiv _ h.property, hLeft h hh, mul_assoc]
  · intro h hh T hT
    refine ⟨hPInvariant _ h.property _ hT.1, ?_⟩
    change f (P (h.val * T)) ∈ Metric.ball M ε
    rw [hPEquiv _ h.property, hLeft h hh]
    exact hT.2

end
end BanachIsometric
