import BanachIsometric.FiniteEquations
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Tactic

/-!
# Compact orthogonal polynomial stabilisers

The orthogonal group is a closed set of real matrices with every entry in
`[-1,1]`, hence compact. Polynomial constraints and full tensor-coordinate
stabiliser conditions are closed. Their intersections with the orthogonal
group are therefore compact, as required in Lemma 2.1(i).

No convexity, central symmetry, or moment normalisation is needed for these
topological facts. Identifying body automorphisms with the relevant orthogonal
stabiliser still requires the covariance and moment arguments.
-/

namespace BanachIsometric

/-- Orthogonal real matrices, expressed by their defining row equations. -/
def orthogonalMatrixSet (m : ℕ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {Q | Q * Q.transpose = 1}

theorem isClosed_orthogonalMatrixSet (m : ℕ) :
    IsClosed (orthogonalMatrixSet m) := by
  exact isClosed_eq (continuous_id.mul continuous_id.matrix_transpose) continuous_const

/-- Every coordinate of an orthogonal real matrix belongs to `[-1,1]`. -/
theorem orthogonalMatrix_entry_bounds {m : ℕ}
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalMatrixSet m)
    (i j : Fin m) : -1 ≤ Q i j ∧ Q i j ≤ 1 := by
  have hdiag : (∑ k : Fin m, Q i k * Q i k) = 1 := by
    have hi := congrArg (fun M : Matrix (Fin m) (Fin m) ℝ => M i i) hQ
    simpa [Matrix.mul_apply] using hi
  have hle : Q i j * Q i j ≤ ∑ k : Fin m, Q i k * Q i k :=
    Finset.single_le_sum (fun k _ => mul_self_nonneg (Q i k)) (Finset.mem_univ j)
  rw [hdiag] at hle
  constructor <;> nlinarith [sq_nonneg (Q i j + 1), sq_nonneg (Q i j - 1)]

theorem isCompact_orthogonalMatrixSet (m : ℕ) :
    IsCompact (orthogonalMatrixSet m) := by
  have hbox : IsCompact (Set.Icc (fun _ _ : Fin m => (-1 : ℝ)) (fun _ _ => (1 : ℝ))) :=
    isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_orthogonalMatrixSet m)
  intro Q hQ
  constructor
  · intro i j
    exact (orthogonalMatrix_entry_bounds hQ i j).1
  · intro i j
    exact (orthogonalMatrix_entry_bounds hQ i j).2

/-- The matrix set used above is the standard orthogonal group in Mathlib. -/
theorem mem_orthogonalMatrixSet_iff (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Q ∈ orthogonalMatrixSet m ↔ Q ∈ Matrix.orthogonalGroup (Fin m) ℝ :=
  (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).symm

/-- Compactness of the actual standard orthogonal-group type with its inherited
matrix topology. This is a theorem rather than a new global typeclass instance. -/
theorem compactSpace_orthogonalGroup (m : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := by
  apply isCompact_iff_compactSpace.mp
  convert isCompact_orthogonalMatrixSet m using 1
  ext Q
  exact (mem_orthogonalMatrixSet_iff m Q).symm

/-- Common zero loci are closed in the coordinate-space topology, for arbitrary
families and even infinitely many variables. -/
def polynomialZeroSet {σ : Type*} (S : Set (MvPolynomial σ ℝ)) : Set (σ → ℝ) :=
  {x | ∀ P ∈ S, MvPolynomial.eval x P = 0}

theorem isClosed_polynomialZeroSet {σ : Type*} (S : Set (MvPolynomial σ ℝ)) :
    IsClosed (polynomialZeroSet S) := by
  have heq : polynomialZeroSet S =
      ⋂ P : S, {x : σ → ℝ | MvPolynomial.eval x P.val = 0} := by
    ext x
    simp [polynomialZeroSet]
  rw [heq]
  exact isClosed_iInter fun P => isClosed_eq P.val.continuous_eval continuous_const

/-- Flatten a real matrix into its list of entry coordinates. -/
def matrixCoordinates {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℝ) : Fin m × Fin m → ℝ :=
  fun ij => Q ij.1 ij.2

theorem continuous_matrixCoordinates (m : ℕ) :
    Continuous (matrixCoordinates (m := m)) := by
  exact continuous_pi fun ij => continuous_apply_apply ij.1 ij.2

/-- Orthogonal matrices satisfying any family of polynomial equations form a
compact set. The family need not be finite for this topological conclusion. -/
theorem isCompact_orthogonal_polynomialZeroSet (m : ℕ)
    (S : Set (MvPolynomial (Fin m × Fin m) ℝ)) :
    IsCompact (orthogonalMatrixSet m ∩ matrixCoordinates ⁻¹' polynomialZeroSet S) :=
  (isCompact_orthogonalMatrixSet m).inter_right
    ((isClosed_polynomialZeroSet S).preimage (continuous_matrixCoordinates m))

theorem continuous_tensorCoordinateAction {m r : ℕ}
    (M : (Fin r → Fin m) → ℝ) (out : Fin r → Fin m) :
    Continuous (fun A : Matrix (Fin m) (Fin m) ℝ => tensorCoordinateAction A M out) := by
  have h := (tensorEntryPolynomial m r M out).continuous_eval.comp
    (continuous_matrixCoordinates m)
  convert h using 1
  funext A
  exact (tensorEntryPolynomial_eval A M out).symm

/-- Matrices fixing every tensor in a family of positive degrees. -/
def tensorStabilizerSet (m : ℕ)
    (M : (d : ℕ+) → (Fin (d : ℕ) → Fin m) → ℝ) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∀ d, tensorCoordinateAction A (M d) = M d}

theorem isClosed_tensorStabilizerSet (m : ℕ)
    (M : (d : ℕ+) → (Fin (d : ℕ) → Fin m) → ℝ) :
    IsClosed (tensorStabilizerSet m M) := by
  have heq : tensorStabilizerSet m M =
      ⋂ d : ℕ+, ⋂ out : Fin (d : ℕ) → Fin m,
        {A : Matrix (Fin m) (Fin m) ℝ | tensorCoordinateAction A (M d) out = M d out} := by
    ext A
    simp [tensorStabilizerSet, funext_iff]
  rw [heq]
  exact isClosed_iInter fun d => isClosed_iInter fun out =>
    isClosed_eq (continuous_tensorCoordinateAction (M d) out) continuous_const

/-- The full orthogonal tensor stabiliser is compact. This applies equally to
odd and even moments of an asymmetric body. -/
theorem isCompact_orthogonal_tensorStabilizerSet (m : ℕ)
    (M : (d : ℕ+) → (Fin (d : ℕ) → Fin m) → ℝ) :
    IsCompact (orthogonalMatrixSet m ∩ tensorStabilizerSet m M) :=
  (isCompact_orthogonalMatrixSet m).inter_right (isClosed_tensorStabilizerSet m M)

/-- The two inclusions whose conjunction expresses preservation of a body by
an orthogonal matrix. Writing the inverse as a transpose makes closedness
immediate from the pointwise action. -/
def twoSidedBodyCondition (m : ℕ) (S : Set (Fin m → ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {Q | (∀ x ∈ S, Q.mulVec x ∈ S) ∧ (∀ x ∈ S, Q.transpose.mulVec x ∈ S)}

theorem orthogonalMatrix_image_eq_iff {m : ℕ} (S : Set (Fin m → ℝ))
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q ∈ orthogonalMatrixSet m) :
    Q.mulVec '' S = S ↔ Q ∈ twoSidedBodyCondition m S := by
  have hleft : Q.transpose * Q = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp
      ((mem_orthogonalMatrixSet_iff m Q).mp hQ)
  constructor
  · intro h
    constructor
    · intro x hx
      rw [← h]
      exact Set.mem_image_of_mem Q.mulVec hx
    · intro y hy
      have hyimage : y ∈ Q.mulVec '' S := by rwa [h]
      obtain ⟨x, hx, hxy⟩ := hyimage
      have hinv : Q.transpose.mulVec y = x := by
        rw [← hxy, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
      rwa [hinv]
  · intro h
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact h.1 x hx
    · intro y hy
      refine ⟨Q.transpose.mulVec y, h.2 y hy, ?_⟩
      rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

theorem isClosed_twoSidedBodyCondition (m : ℕ) {S : Set (Fin m → ℝ)}
    (hS : IsClosed S) : IsClosed (twoSidedBodyCondition m S) := by
  have hf : IsClosed {Q : Matrix (Fin m) (Fin m) ℝ | ∀ x ∈ S, Q.mulVec x ∈ S} := by
    have heq : {Q : Matrix (Fin m) (Fin m) ℝ | ∀ x ∈ S, Q.mulVec x ∈ S} =
        ⋂ x : S, {Q : Matrix (Fin m) (Fin m) ℝ | Q.mulVec x.val ∈ S} := by
      ext Q
      simp
    rw [heq]
    exact isClosed_iInter fun x =>
      hS.preimage (continuous_id.matrix_mulVec continuous_const)
  have hi : IsClosed {Q : Matrix (Fin m) (Fin m) ℝ |
      ∀ x ∈ S, Q.transpose.mulVec x ∈ S} := by
    have heq : {Q : Matrix (Fin m) (Fin m) ℝ | ∀ x ∈ S, Q.transpose.mulVec x ∈ S} =
        ⋂ x : S, {Q : Matrix (Fin m) (Fin m) ℝ | Q.transpose.mulVec x.val ∈ S} := by
      ext Q
      simp
    rw [heq]
    exact isClosed_iInter fun x =>
      hS.preimage (continuous_id.matrix_transpose.matrix_mulVec continuous_const)
  exact hf.inter hi

/-- Orthogonal symmetries of a closed body form a compact set. This direct
argument does not need moment separation or finite moment generation. -/
theorem isCompact_orthogonal_bodyStabilizer (m : ℕ) {S : Set (Fin m → ℝ)}
    (hS : IsClosed S) :
    IsCompact {Q : Matrix (Fin m) (Fin m) ℝ |
      Q ∈ orthogonalMatrixSet m ∧ Q.mulVec '' S = S} := by
  have heq : {Q : Matrix (Fin m) (Fin m) ℝ |
      Q ∈ orthogonalMatrixSet m ∧ Q.mulVec '' S = S} =
        orthogonalMatrixSet m ∩ twoSidedBodyCondition m S := by
    ext Q
    constructor
    · rintro ⟨hQ, h⟩
      exact ⟨hQ, (orthogonalMatrix_image_eq_iff S hQ).mp h⟩
    · rintro ⟨hQ, h⟩
      exact ⟨hQ, (orthogonalMatrix_image_eq_iff S hQ).mpr h⟩
  rw [heq]
  exact (isCompact_orthogonalMatrixSet m).inter_right
    (isClosed_twoSidedBodyCondition m hS)

/-- The actual subgroup of the standard orthogonal group preserving a body. -/
def orthogonalBodyStabilizerSubgroup (m : ℕ) (S : Set (Fin m → ℝ)) :
    Subgroup (Matrix.orthogonalGroup (Fin m) ℝ) where
  carrier := {Q | (Q.val.mulVec '' S) = S}
  one_mem' := by
    change (1 : Matrix (Fin m) (Fin m) ℝ).mulVec '' S = S
    ext x
    simp
  mul_mem' := by
    intro A B hA hB
    have hfun : (A * B).val.mulVec = A.val.mulVec ∘ B.val.mulVec := by
      funext x
      exact (Matrix.mulVec_mulVec x A.val B.val).symm
    change (A * B).val.mulVec '' S = S
    calc
      (A * B).val.mulVec '' S = A.val.mulVec '' (B.val.mulVec '' S) := by
        rw [Set.image_image]
        exact congrArg (fun f : (Fin m → ℝ) → Fin m → ℝ => f '' S) hfun
      _ = S := by rw [hB, hA]
  inv_mem' := by
    intro A hA
    have hprod : (A⁻¹).val * A.val = (1 : Matrix (Fin m) (Fin m) ℝ) :=
      congrArg Subtype.val (inv_mul_cancel A)
    have hfun : (A⁻¹).val.mulVec ∘ A.val.mulVec = id := by
      funext x
      exact (Matrix.mulVec_mulVec x (A⁻¹).val A.val).trans
        (by rw [hprod, Matrix.one_mulVec]; rfl)
    change (A⁻¹).val.mulVec '' S = S
    calc
      (A⁻¹).val.mulVec '' S = (A⁻¹).val.mulVec '' (A.val.mulVec '' S) := by rw [hA]
      _ = S := by
        rw [Set.image_image]
        change ((A⁻¹).val.mulVec ∘ A.val.mulVec) '' S = S
        rw [hfun, Set.image_id]

theorem isClosed_orthogonalBodyStabilizerSubgroup (m : ℕ)
    {S : Set (Fin m → ℝ)} (hS : IsClosed S) :
    IsClosed (orthogonalBodyStabilizerSubgroup m S : Set (Matrix.orthogonalGroup (Fin m) ℝ)) := by
  have heq : (orthogonalBodyStabilizerSubgroup m S : Set (Matrix.orthogonalGroup (Fin m) ℝ)) =
      Subtype.val ⁻¹' twoSidedBodyCondition m S := by
    ext Q
    exact orthogonalMatrix_image_eq_iff S
      ((mem_orthogonalMatrixSet_iff m Q.val).mpr Q.property)
  rw [heq]
  exact (isClosed_twoSidedBodyCondition m hS).preimage continuous_subtype_val

/-- Closed-body symmetries are a compact subgroup of `O(m)`, with no central
symmetry or convexity assumption on the body. -/
theorem compactSpace_orthogonalBodyStabilizerSubgroup (m : ℕ)
    {S : Set (Fin m → ℝ)} (hS : IsClosed S) :
    CompactSpace (orthogonalBodyStabilizerSubgroup m S) := by
  letI : CompactSpace (Matrix.orthogonalGroup (Fin m) ℝ) := compactSpace_orthogonalGroup m
  exact isCompact_iff_compactSpace.mp (isClosed_orthogonalBodyStabilizerSubgroup m hS).isCompact

end BanachIsometric
