import BanachIsometric.StabilizerRetraction
import BanachIsometric.NormalizedImageMoments
import Mathlib.Topology.Algebra.Module.Star

/-!
# Lipschitz equivariant retraction onto the actual moment stabilizer

The actual inverse orbit map is a polynomial map of the matrix and its real
transpose. Compactness of the orthogonal group gives a global Lipschitz bound.
The proved orbit section therefore strengthens the explicit stabilizer
retraction to a Lipschitz retraction on an open invariant neighbourhood.
-/

namespace BanachIsometric

open Set Filter MeasureTheory
open scoped Topology NNReal Matrix.Norms.Operator

noncomputable section

section QuantitativeHelpers

variable {P A : Type*} [PseudoMetricSpace P] [NormedRing A]

theorem lipschitzOnWith_ring_mul_of_norm_bounds {U : Set P} {f g : P → A}
    {KF KG MF MG : ℝ≥0} (hf : LipschitzOnWith KF f U) (hg : LipschitzOnWith KG g U)
    (hMf : ∀ x ∈ U, ‖f x‖ ≤ MF) (hMg : ∀ x ∈ U, ‖g x‖ ≤ MG) :
    LipschitzOnWith (MF * KG + KF * MG) (fun x => f x * g x) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hdec : f x * g x - f y * g y = f x * (g x - g y) + (f x - f y) * g y := by
    rw [mul_sub, sub_mul]
    abel
  have hfd : ‖f x - f y‖ ≤ KF * dist x y := by
    simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy
  have hgd : ‖g x - g y‖ ≤ KG * dist x y := by
    simpa only [dist_eq_norm] using hg.dist_le_mul x hx y hy
  rw [dist_eq_norm, hdec]
  calc
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ MF * (KG * dist x y) + (KF * dist x y) * MG := by
      exact add_le_add (mul_le_mul (hMf x hx) hgd (norm_nonneg _) MF.coe_nonneg)
        (mul_le_mul hfd (hMg y hy) (norm_nonneg _) (mul_nonneg KF.coe_nonneg dist_nonneg))
    _ = _ := by push_cast; ring

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_lipschitzOnWith_contDiff_compact {f : E → W} (hf : ContDiff ℝ ⊤ f)
    {S : Set E} (hS : IsCompact S) : ∃ L : ℝ≥0, LipschitzOnWith L f S := by
  obtain ⟨R, hSR⟩ := hS.isBounded.subset_closedBall (0 : E)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) R).bddAbove_image
    (hf.continuous_fderiv (by simp)).norm.continuousOn
  let L : ℝ≥0 := ⟨max 0 B, le_max_left _ _⟩
  have hbound : ∀ x ∈ Metric.closedBall (0 : E) R, ‖fderiv ℝ f x‖₊ ≤ L := by
    intro x hx
    change ‖fderiv ℝ f x‖ ≤ max 0 B
    exact (hB (mem_image_of_mem (fun y => ‖fderiv ℝ f y‖) hx)).trans (le_max_right _ _)
  exact ⟨L, (Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun _ _ => (hf.differentiable (by simp)).differentiableAt) hbound
    (convex_closedBall (0 : E) R)).mono hSR⟩

end QuantitativeHelpers

def tensorInverseOrbit (m : ℕ) (I : Finset ℕ+) (M : TensorTupleCoordinates m I)
    (Q : Matrix.orthogonalGroup (Fin m) ℝ) : TensorTupleCoordinates m I := Q⁻¹ • M

theorem exists_lipschitz_tensorInverseOrbit (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) : ∃ L : ℝ≥0, LipschitzWith L (tensorInverseOrbit m I M) := by
  letI : CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := compactSpace_orthogonalGroup m
  let f : Matrix (Fin m) (Fin m) ℝ → TensorTupleCoordinates m I :=
    fun A => tensorTupleLinearRepresentation m I (star A) M
  have hf : ContDiff ℝ ⊤ f :=
    (contDiff_tensorTupleOrbit m I M).comp (starL' ℝ).contDiff
  have hCompact : IsCompact (Set.range
      (fun Q : Matrix.orthogonalGroup (Fin m) ℝ => Q.val)) :=
    isCompact_range continuous_subtype_val
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_contDiff_compact hf hCompact
  refine ⟨L, LipschitzWith.of_dist_le_mul ?_⟩
  intro Q R
  have h := hL.dist_le_mul Q.val ⟨Q, rfl⟩ R.val ⟨R, rfl⟩
  simpa only [f, tensorInverseOrbit, tensorTupleOrthogonal_smul_def,
    Matrix.UnitaryGroup.inv_val] using h

/-- A genuine Lipschitz retraction onto the actual tensor stabilizer, on an
open left-invariant neighbourhood of that stabilizer inside the actual
orthogonal group. The orbit section and all quantitative inputs are proved.
-/
theorem exists_lipschitz_tensorTuple_stabilizer_retraction (m : ℕ) (I : Finset ℕ+)
    (M : TensorTupleCoordinates m I) :
    ∃ U : Set (Matrix.orthogonalGroup (Fin m) ℝ),
      ∃ r : Matrix.orthogonalGroup (Fin m) ℝ → Matrix.orthogonalGroup (Fin m) ℝ,
      ∃ L : ℝ≥0, IsOpen U ∧
        (MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M : Set _) ⊆ U ∧
        LipschitzOnWith L r U ∧
        (∀ g ∈ U, r g ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M) ∧
        (∀ h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M, r h = h) ∧
        (∀ h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M,
          ∀ g, r (h * g) = h * r g) ∧
        (∀ h ∈ MulAction.stabilizer (Matrix.orthogonalGroup (Fin m) ℝ) M,
          ∀ g ∈ U, h * g ∈ U) := by
  classical
  let O := Matrix.orthogonalGroup (Fin m) ℝ
  letI : CompactSpace O := compactSpace_orthogonalGroup m
  obtain ⟨q, N, hN, KQ, hqM, hqLip, hqSect⟩ := exists_lipschitz_tensorTuple_orbit_section m I M
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨KC, hcLip⟩ := exists_lipschitz_tensorInverseOrbit m I M
  let c := tensorInverseOrbit m I M
  let U : Set O := c ⁻¹' Metric.ball M ε
  let r : O → O := stabilizerRetraction M q
  have hU : IsOpen U := Metric.isOpen_ball.preimage hcLip.continuous
  have hContains : (MulAction.stabilizer O M : Set O) ⊆ U := by
    intro h hh
    have hinv : h⁻¹ • M = M := (MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer O M).inv_mem hh)
    change dist (h⁻¹ • M) M < ε
    simpa only [hinv, dist_self] using hε
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.bddAbove_image
    (continuous_subtype_val : Continuous (fun Q : O => Q.val)).norm.continuousOn
  let B : ℝ≥0 := ⟨max 0 B₀, le_max_left _ _⟩
  have hBound : ∀ Q : O, ‖Q.val‖ ≤ B := fun Q =>
    (hB₀ (mem_image_of_mem (fun R : O => ‖R.val‖) (mem_univ Q))).trans (le_max_right _ _)
  have hID : LipschitzOnWith 1 (fun Q : O => Q.val) U :=
    isometry_subtype_coe.lipschitz.lipschitzOnWith
  have hQC : LipschitzOnWith (KQ * KC) (fun Q : O => (q (c Q)).val) U :=
    hqLip.comp hcLip.lipschitzOnWith (fun _ h => hball h)
  have hrLip : LipschitzOnWith (B * (KQ * KC) + 1 * B) r U :=
    lipschitzOnWith_ring_mul_of_norm_bounds hID hQC
      (fun Q _ => hBound Q) (fun Q _ => hBound (q (c Q)))
  refine ⟨U, r, B * (KQ * KC) + 1 * B, hU, hContains, hrLip, ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply MulAction.mem_stabilizer_iff.mpr
    exact stabilizerRetraction_smul_eq M q (hqSect (c g) (hball hg) ⟨g⁻¹, rfl⟩)
  · intro h hh
    exact stabilizerRetraction_fixed M q hqM hh
  · intro h hh g
    exact stabilizerRetraction_equivariant M q hh g
  · intro h hh g hg
    have hinv : h⁻¹ • M = M := (MulAction.mem_stabilizer_iff).mp
      ((MulAction.stabilizer O M).inv_mem hh)
    change dist ((h * g)⁻¹ • M) M < ε
    simpa only [mul_inv_rev, mul_smul, hinv] using hg

end
end BanachIsometric
