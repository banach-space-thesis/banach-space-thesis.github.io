import NonCalkinAlgebra.MatrixIdeal
import NonCalkinAlgebra.MatrixEntrySeparation
import NonCalkinAlgebra.ClosedIdealSubmodule
import NonCalkinAlgebra.PrerequisiteStatements

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace NonCalkinAlgebra
universe u
variable (D : Type u) [NormedRing D] [NormedAlgebra ℂ D] [NormOneClass D]

def matrixThetaMap (i j : ℕ) : D →L[ℂ] matrixAlgebra D :=
  (thetaCoefficientMap D i j).codRestrict (matrixAlgebra D).toSubmodule
    (fun d => theta_mem_matrixAlgebra D i j d)

@[simp] theorem matrixThetaMap_apply (i j : ℕ) (d : D) :
    matrixThetaMap D i j d = matrixTheta D i j d := rfl

theorem matrixTheta_mul (i j k l : ℕ) (d e : D) :
    matrixTheta D i j d * matrixTheta D k l e =
      if j = k then matrixTheta D i l (d * e) else 0 := by
  classical
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, coe_matrixTheta]
  split_ifs with h
  · exact (theta_mul D i j k l d e).trans (if_pos h)
  · exact (theta_mul D i j k l d e).trans (if_neg h)

def entryIdeal (I : TwoSidedIdeal (matrixAlgebra D)) (r s : ℕ) : TwoSidedIdeal D :=
  TwoSidedIdeal.mk' {d | matrixThetaMap D r s d ∈ I}
    (by simpa only [Set.mem_setOf_eq, map_zero] using I.zero_mem)
    (fun ha hb => by simpa only [Set.mem_setOf_eq, map_add] using I.add_mem ha hb)
    (fun ha => by simpa only [Set.mem_setOf_eq, map_neg] using I.neg_mem ha)
    (fun {b d} hd => by
      have h := I.mul_mem_left (matrixTheta D r r b) (matrixTheta D r s d) hd
      simpa only [matrixThetaMap_apply, matrixTheta_mul, if_pos rfl] using h)
    (fun {d b} hd => by
      have h := I.mul_mem_right (matrixTheta D r s d) (matrixTheta D s s b) hd
      simpa only [matrixThetaMap_apply, matrixTheta_mul, if_pos rfl] using h)

@[simp] theorem mem_entryIdeal (I : TwoSidedIdeal (matrixAlgebra D)) (r s : ℕ) (d : D) :
    d ∈ entryIdeal D I r s ↔ matrixTheta D r s d ∈ I := by
  simp only [entryIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq, matrixThetaMap_apply]

theorem entryIdeal_isClosed (I : TwoSidedIdeal (matrixAlgebra D))
    (hI : IsClosed (I : Set (matrixAlgebra D))) (r s : ℕ) :
    IsClosed (entryIdeal D I r s : Set D) := by
  have h := hI.preimage (matrixThetaMap D r s).continuous
  simpa only [entryIdeal, TwoSidedIdeal.coe_mk'] using h

theorem matrixIdeal_contains_matrices_of_ne_bot (hD : IsTopologicallySimple D)
    (I : TwoSidedIdeal (matrixAlgebra D)) (hI : IsClosed (I : Set (matrixAlgebra D)))
    (hIJ : I ≤ matrixIdeal D) (hzero : I ≠ ⊥) :
    ∀ i j : ℕ, ∀ d : D, matrixTheta D i j d ∈ I := by
  classical
  have hexists : ∃ a : matrixAlgebra D, a ∈ I ∧ a ≠ 0 := by
    by_contra! h
    apply hzero
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using h a ha
  obtain ⟨a, ha, hane⟩ := hexists
  have haJ := (mem_matrixIdeal D a).mp (hIJ ha)
  have haneOp : (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) ≠ 0 := by
    intro h
    exact hane (Subtype.ext h)
  obtain ⟨r, s, hrs⟩ := matrixClosure_has_nonzero_entry D haJ haneOp
  have hcorner : matrixTheta D r s (matrixEntry D r s a) ∈ I := by
    have h := I.mul_mem_right
      (matrixTheta D r r 1 * a) (matrixTheta D s s 1)
      (I.mul_mem_left (matrixTheta D r r 1) a ha)
    have heq : matrixTheta D r r 1 * a * matrixTheta D s s 1 =
        matrixTheta D r s (matrixEntry D r s a) := by
      apply Subtype.ext
      exact matrixClosure_corner_formula D haJ r s
    rwa [heq] at h
  have hKtop : entryIdeal D I r s = ⊤ := by
    rcases hD (entryIdeal D I r s) (entryIdeal_isClosed D I hI r s) with hbot | htop
    · have hmem := (mem_entryIdeal D I r s _).mpr hcorner
      rw [hbot, TwoSidedIdeal.mem_bot] at hmem
      exact False.elim (hrs hmem)
    · exact htop
  intro i j d
  have hd : d ∈ entryIdeal D I r s := by rw [hKtop]; trivial
  have hmiddle := (mem_entryIdeal D I r s d).mp hd
  have h := I.mul_mem_right
    (matrixTheta D i r 1 * matrixTheta D r s d) (matrixTheta D s j 1)
    (I.mul_mem_left (matrixTheta D i r 1) _ hmiddle)
  simpa only [matrixTheta_mul, if_true, one_mul, mul_one] using h

def matrixIdealImage (I : TwoSidedIdeal (matrixAlgebra D)) :
    Submodule ℂ (CoefficientSpace D →L[ℂ] CoefficientSpace D) :=
    { carrier := {T | ∃ a : matrixAlgebra D, a ∈ I ∧
        (a : CoefficientSpace D →L[ℂ] CoefficientSpace D) = T}
      zero_mem' := ⟨0, I.zero_mem, rfl⟩
      add_mem' := by
        rintro T U ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, I.add_mem ha hb, rfl⟩
      smul_mem' := by
        rintro c T ⟨a, ha, rfl⟩
        exact ⟨c • a, twoSidedIdeal_smul_mem (A := matrixAlgebra D) I ha c, rfl⟩ }

/-- The simplicity argument from Proposition 5.1, in the exact ambient algebra A_D. -/
theorem matrixIdeal_simple_below (hD : IsTopologicallySimple D)
    (I : TwoSidedIdeal (matrixAlgebra D)) (hI : IsClosed (I : Set (matrixAlgebra D)))
    (hIJ : I ≤ matrixIdeal D) : I = ⊥ ∨ I = matrixIdeal D := by
  by_cases hzero : I = ⊥
  · exact Or.inl hzero
  have hall := matrixIdeal_contains_matrices_of_ne_bot D hD I hI hIJ hzero
  let W := matrixIdealImage D I
  have hWclosed : IsClosed (W : Set (CoefficientSpace D →L[ℂ] CoefficientSpace D)) :=
    (matrixAlgebra_isClosed D).isClosedMap_subtype_val (I : Set (matrixAlgebra D)) hI
  have hgen : matrixGenerators D ⊆ W := by
    rintro T ⟨i, j, d, rfl⟩
    exact ⟨matrixTheta D i j d, hall i j d, rfl⟩
  have hspan : finiteMatrixSpan D ≤ W := Submodule.span_le.mpr hgen
  have hclosure : matrixClosure D ≤ W :=
    Submodule.topologicalClosure_minimal (finiteMatrixSpan D) hspan hWclosed
  refine Or.inr (le_antisymm hIJ ?_)
  intro b hb
  obtain ⟨c, hc, heq⟩ := hclosure ((mem_matrixIdeal D b).mp hb)
  have hcb : c = b := Subtype.ext heq
  simpa only [hcb] using hc

/-- Proposition 5.1: the constructed algebra has exactly one nonzero proper
closed two-sided ideal. No coefficient-algebra existence result is assumed here. -/
theorem matrixAlgebra_has_exactly_one_ideal (hD : IsTopologicallySimple D) :
    HasExactlyOneNonzeroProperClosedIdeal (matrixAlgebra D) := by
  apply one_ideal_of_scalar_extension (matrixIdeal D) (matrixIdeal_isNonzeroProperClosed D)
  · intro a
    obtain ⟨c, j, hj, heq⟩ := (mem_unitizedMatrixSubspace D a).mp a.property
    let b : matrixAlgebra D := ⟨j, matrixClosure_mem_matrixAlgebra D hj⟩
    exact ⟨c, b, (mem_matrixIdeal D b).mpr hj, Subtype.ext heq⟩
  · exact matrixIdeal_simple_below D hD
  · exact matrixIdeal_has_no_identity D

end NonCalkinAlgebra
