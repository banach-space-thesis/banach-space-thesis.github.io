import JLMS.FiniteRank
import JLMS.Adjoint
import JLMS.MainStatements

/-!
# Finite-dimensional cases of the main results

Section 8 uses a complemented copy of c₀. That construction requires infinite K.
For finite K, C₀(K) is finite-dimensional and its Calkin algebra is zero.
The arguments below cover this case directly, including empty K. The general
finite-dimensional lemmas are reusable independently of scattered spaces.
-/

noncomputable section

namespace JLMS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Every bounded map from a finite-dimensional space has finite rank. -/
theorem isCompactOperator_of_finiteDimensional_domain [FiniteDimensional 𝕜 E]
    (T : E →L[𝕜] F) : IsCompactOperator T :=
  isCompactOperator_of_finiteRank T inferInstance

/-- Essential norm vanishes for finite-dimensional domains; no completeness
of the range is needed. -/
theorem essentialNorm_eq_zero_of_finiteDimensional [FiniteDimensional 𝕜 E]
    (T : E →L[𝕜] F) : essentialNorm T = 0 := by
  apply le_antisymm _ (essentialNorm_nonneg T)
  simpa using essentialNorm_le_norm_sub T T
    (isCompactOperator_of_finiteDimensional_domain T)

/-- Every class in the Calkin quotient of a finite-dimensional space is zero. -/
theorem calkin_eq_zero_of_finiteDimensional [FiniteDimensional 𝕜 E]
    (x : Calkin 𝕜 E) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H T =>
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (isCompactOperator_of_finiteDimensional_domain T)

/-- Minimality on a zero Calkin algebra is automatic. -/
theorem essentialNormIsMinimal_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    EssentialNormIsMinimal 𝕜 E := by
  intro n hn
  refine ⟨1, zero_lt_one, ?_⟩
  intro T
  simpa [essentialNorm_eq_zero_of_finiteDimensional T] using hn.1.1 (calkinMk 𝕜 E T)

/-- All vector norms on the zero Calkin quotient coincide. -/
theorem hasUniqueCalkinNorm_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    HasUniqueCalkinNorm 𝕜 E := by
  intro n m hn hm
  refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
  intro x
  have hn0 := (hn.1.2.1 x).mpr (calkin_eq_zero_of_finiteDimensional x)
  have hm0 := (hm.1.2.1 x).mpr (calkin_eq_zero_of_finiteDimensional x)
  simp [hn0, hm0]

theorem hasUniqueCompleteCalkinNorm_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    HasUniqueCompleteCalkinNorm 𝕜 E := by
  intro n m hn hm _ _
  exact hasUniqueCalkinNorm_of_finiteDimensional n m hn hm

/-- The adjoint of a map into a finite-dimensional space is compact. -/
theorem dualEssentialNorm_eq_zero_of_finiteDimensional_range [FiniteDimensional 𝕜 F]
    (T : E →L[𝕜] F) : dualEssentialNorm T = 0 := by
  exact essentialNorm_eq_zero_of_finiteDimensional (banachAdjoint T)

theorem bonsallMinimality_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    DualEssentialNormHasBonsallMinimality 𝕜 E := by
  intro n hn _ T
  rw [(hn.1.2.1 _).mpr (calkin_eq_zero_of_finiteDimensional _),
    dualEssentialNorm_eq_zero_of_finiteDimensional_range T]

variable {K : Type*} [TopologicalSpace K]

/-- Evaluation embeds C₀(K) linearly into the finite-dimensional function space. -/
theorem finiteDimensional_CZero_of_finite [Finite K] : FiniteDimensional 𝕜 (CZero 𝕜 K) := by
  letI : Fintype K := Fintype.ofFinite K
  let J : CZero 𝕜 K →ₗ[𝕜] (K → 𝕜) :=
    { toFun := fun f k => f k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective J (by
    intro f g h
    ext k
    exact congrFun h k)

/-- Theorem 1.1, including its complete-uniqueness clause, for finite K. -/
theorem theorem_1_1_of_finite [LocallyCompactSpace K] [T2Space K] [Finite K] :
    Theorem_1_1 𝕜 K := by
  letI := finiteDimensional_CZero_of_finite (𝕜 := 𝕜) (K := K)
  intro _
  exact ⟨essentialNormIsMinimal_of_finiteDimensional,
    hasUniqueCompleteCalkinNorm_of_finiteDimensional⟩

/-- Theorem 1.5 for finite K. -/
theorem theorem_1_5_of_finite [LocallyCompactSpace K] [T2Space K] [Finite K] :
    Theorem_1_5 𝕜 K := by
  letI := finiteDimensional_CZero_of_finite (𝕜 := 𝕜) (K := K)
  intro _
  exact bonsallMinimality_of_finiteDimensional

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- There are no noncompact operators with finite K, so Theorem 1.6 is vacuous. -/
theorem theorem_1_6_of_finite [LocallyCompactSpace K] [T2Space K] [Finite K] :
    Theorem_1_6 𝕜 K X := by
  letI := finiteDimensional_CZero_of_finite (𝕜 := 𝕜) (K := K)
  intro _ _ T hT
  exact (hT (isCompactOperator_of_finiteDimensional_domain T)).elim

theorem theorem_1_7_of_finite [LocallyCompactSpace K] [T2Space K] [Finite K] :
    Theorem_1_7 𝕜 K X := by
  letI := finiteDimensional_CZero_of_finite (𝕜 := 𝕜) (K := K)
  intro _ _ T hT
  exact (hT (isCompactOperator_of_finiteDimensional_domain T)).elim

end JLMS
