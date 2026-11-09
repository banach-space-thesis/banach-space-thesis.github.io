import NonCalkinAlgebra.MatrixIdealStructure
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

/-- The nonunital Banach algebra J_D itself, rather than its ideal lattice
inside A_D. Its elements and its norm are the literal closed matrix operators. -/
def matrixNonunitalAlgebra : NonUnitalSubalgebra ℂ
    (CoefficientSpace D →L[ℂ] CoefficientSpace D) where
  toSubmodule := matrixClosure D
  mul_mem' := matrixClosure_mul D

instance [CompleteSpace D] : CompleteSpace (matrixNonunitalAlgebra D) :=
  (matrixClosure_isClosed D).completeSpace_coe

def nonunitalThetaMap (i j : ℕ) : D →L[ℂ] matrixNonunitalAlgebra D :=
  (thetaCoefficientMap D i j).codRestrict (matrixNonunitalAlgebra D).toSubmodule
    (fun d => theta_mem_matrixClosure D i j d)

@[simp] theorem coe_nonunitalThetaMap (i j : ℕ) (d : D) :
    ((nonunitalThetaMap D i j d : matrixNonunitalAlgebra D) :
      CoefficientSpace D →L[ℂ] CoefficientSpace D) = theta D i j d := rfl

theorem nonunitalThetaMap_mul (i j k l : ℕ) (d e : D) :
    nonunitalThetaMap D i j d * nonunitalThetaMap D k l e =
      if j = k then nonunitalThetaMap D i l (d * e) else 0 := by
  classical
  apply Subtype.ext
  split_ifs with h
  · exact (theta_mul D i j k l d e).trans (if_pos h)
  · exact (theta_mul D i j k l d e).trans (if_neg h)

def nonunitalEntryIdeal (I : TwoSidedIdeal (matrixNonunitalAlgebra D))
    (r s : ℕ) : TwoSidedIdeal D :=
  TwoSidedIdeal.mk' {d | nonunitalThetaMap D r s d ∈ I}
    (by simpa only [Set.mem_setOf_eq, map_zero] using I.zero_mem)
    (fun ha hb => by simpa only [Set.mem_setOf_eq, map_add] using I.add_mem ha hb)
    (fun ha => by simpa only [Set.mem_setOf_eq, map_neg] using I.neg_mem ha)
    (fun {b d} hd => by
      have h := I.mul_mem_left (nonunitalThetaMap D r r b) (nonunitalThetaMap D r s d) hd
      simpa only [nonunitalThetaMap_mul, if_pos rfl] using h)
    (fun {d b} hd => by
      have h := I.mul_mem_right (nonunitalThetaMap D r s d) (nonunitalThetaMap D s s b) hd
      simpa only [nonunitalThetaMap_mul, if_pos rfl] using h)

@[simp] theorem mem_nonunitalEntryIdeal (I : TwoSidedIdeal (matrixNonunitalAlgebra D))
    (r s : ℕ) (d : D) : d ∈ nonunitalEntryIdeal D I r s ↔ nonunitalThetaMap D r s d ∈ I := by
  simp only [nonunitalEntryIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

theorem nonunitalEntryIdeal_isClosed (I : TwoSidedIdeal (matrixNonunitalAlgebra D))
    (hI : IsClosed (I : Set (matrixNonunitalAlgebra D))) (r s : ℕ) :
    IsClosed (nonunitalEntryIdeal D I r s : Set D) := by
  simpa only [nonunitalEntryIdeal, TwoSidedIdeal.coe_mk'] using
    hI.preimage (nonunitalThetaMap D r s).continuous

theorem nonunitalIdeal_contains_matrices (hD : IsTopologicallySimple D)
    (I : TwoSidedIdeal (matrixNonunitalAlgebra D))
    (hI : IsClosed (I : Set (matrixNonunitalAlgebra D))) (hne : I ≠ ⊥) :
    ∀ i j : ℕ, ∀ d : D, nonunitalThetaMap D i j d ∈ I := by
  classical
  have hex : ∃ a : matrixNonunitalAlgebra D, a ∈ I ∧ a ≠ 0 := by
    by_contra! h
    apply hne
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using h a ha
  obtain ⟨a, ha, hane⟩ := hex
  have haneOp : (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) ≠ 0 :=
    fun h => hane (Subtype.ext h)
  obtain ⟨r, s, hrs⟩ := matrixClosure_has_nonzero_entry D a.property haneOp
  have hcorner : nonunitalThetaMap D r s (matrixEntry D r s a) ∈ I := by
    have h := I.mul_mem_right
      (nonunitalThetaMap D r r 1 * a) (nonunitalThetaMap D s s 1)
      (I.mul_mem_left (nonunitalThetaMap D r r 1) a ha)
    have heq : nonunitalThetaMap D r r 1 * a * nonunitalThetaMap D s s 1 =
        nonunitalThetaMap D r s (matrixEntry D r s a) := by
      apply Subtype.ext
      exact matrixClosure_corner_formula D a.property r s
    rwa [heq] at h
  have htop : nonunitalEntryIdeal D I r s = ⊤ := by
    rcases hD _ (nonunitalEntryIdeal_isClosed D I hI r s) with hz | ht
    · have hmem := (mem_nonunitalEntryIdeal D I r s _).mpr hcorner
      rw [hz, TwoSidedIdeal.mem_bot] at hmem
      exact False.elim (hrs hmem)
    · exact ht
  intro i j d
  have hd : d ∈ nonunitalEntryIdeal D I r s := by rw [htop]; trivial
  have h := I.mul_mem_right
    (nonunitalThetaMap D i r 1 * nonunitalThetaMap D r s d) (nonunitalThetaMap D s j 1)
    (I.mul_mem_left (nonunitalThetaMap D i r 1) _
      ((mem_nonunitalEntryIdeal D I r s d).mp hd))
  simpa only [nonunitalThetaMap_mul, if_true, one_mul, mul_one] using h

/-- A closed linear core of the ambient image of a nonunital ring ideal.
Using every scalar multiple avoids silently assuming scalar closure for an
arbitrary ring ideal in a nonunital algebra. -/
def nonunitalIdealLinearCore (I : TwoSidedIdeal (matrixNonunitalAlgebra D)) :
    Submodule ℂ (CoefficientSpace D →L[ℂ] CoefficientSpace D) where
  carrier := {T | ∀ c : ℂ, ∃ a : matrixNonunitalAlgebra D, a ∈ I ∧
    (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) = c • T}
  zero_mem' := fun c => ⟨0, I.zero_mem, by simp only [smul_zero]; rfl⟩
  add_mem' := by
    intro T U hT hU c
    obtain ⟨a, ha, hea⟩ := hT c
    obtain ⟨b, hb, heb⟩ := hU c
    refine ⟨a + b, I.add_mem ha hb, ?_⟩
    change (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) +
      (b : CoefficientSpace D →L[ℂ] CoefficientSpace D) = c • (T + U)
    rw [hea, heb, smul_add]
  smul_mem' := by
    intro c T hT b
    obtain ⟨a, ha, hea⟩ := hT (b * c)
    exact ⟨a, ha, by rw [hea, mul_smul]⟩

theorem nonunitalIdealLinearCore_isClosed (I : TwoSidedIdeal (matrixNonunitalAlgebra D))
    (hI : IsClosed (I : Set (matrixNonunitalAlgebra D))) :
    IsClosed (nonunitalIdealLinearCore D I :
      Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) := by
  let U : Set (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
    Subtype.val '' (I : Set (matrixNonunitalAlgebra D))
  have hU : IsClosed U :=
    (matrixClosure_isClosed D).isClosedMap_subtype_val (I : Set (matrixNonunitalAlgebra D)) hI
  have heq : (nonunitalIdealLinearCore D I :
      Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) =
      ⋂ c : ℂ, (fun T => c • T) ⁻¹' U := by
    ext T
    change (∀ c : ℂ, ∃ a : matrixNonunitalAlgebra D, a ∈ I ∧
      (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) = c • T) ↔ _
    simp only [Set.mem_iInter, Set.mem_preimage, U, Set.mem_image]
    rfl
  rw [heq]
  exact isClosed_iInter (fun c => hU.preimage (continuous_const.smul continuous_id))

/-- Proposition 5.1, including the intrinsic simplicity of J_D itself. -/
theorem matrixNonunitalAlgebra_simple (hD : IsTopologicallySimple D)
    (I : TwoSidedIdeal (matrixNonunitalAlgebra D))
    (hI : IsClosed (I : Set (matrixNonunitalAlgebra D))) : I = ⊥ ∨ I = ⊤ := by
  by_cases hz : I = ⊥
  · exact Or.inl hz
  have hall := nonunitalIdeal_contains_matrices D hD I hI hz
  let W := nonunitalIdealLinearCore D I
  have hgen : matrixGenerators D ⊆ W := by
    rintro T ⟨i, j, d, rfl⟩ c
    refine ⟨nonunitalThetaMap D i j (c • d), hall i j (c • d), ?_⟩
    exact (thetaCoefficientMap D i j).map_smul c d
  have hclosure : matrixClosure D ≤ W := Submodule.topologicalClosure_minimal
    (finiteMatrixSpan D) (Submodule.span_le.mpr hgen) (nonunitalIdealLinearCore_isClosed D I hI)
  refine Or.inr (le_antisymm le_top ?_)
  intro a ha
  obtain ⟨b, hb, heq⟩ := hclosure a.property (1 : ℂ)
  have hba : b = a := Subtype.ext (by simpa only [one_smul] using heq)
  simpa only [hba] using hb

theorem matrixNonunitalAlgebra_nonunital :
    ¬ ∃ U : matrixNonunitalAlgebra D,
      ∀ a : matrixNonunitalAlgebra D, U * a = a ∧ a * U = a := by
  rintro ⟨U, hU⟩
  apply matrixClosure_has_no_identity D
  refine ⟨U, U.property, ?_⟩
  intro T hT
  have h := hU ⟨T, hT⟩
  exact ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩

end NonCalkinAlgebra
