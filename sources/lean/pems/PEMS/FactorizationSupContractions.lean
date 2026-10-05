import PEMS.Definitions
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Factorization suprema decrease under contractive compositions. The
factor space is nontrivial, so an identity factorization has nonzero factors;
all inverse-norm inequalities are justified from their actual norms. -/
noncomputable section
open Set
namespace PEMS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G H Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [Nontrivial Z]

private theorem identity_factorization_norm_bound (T : E →L[𝕜] F)
    (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (h : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z) :
    1 ≤ ‖U‖ * ‖T‖ * ‖V‖ := by
  calc
    1 = ‖U.comp (T.comp V)‖ := by rw [h]; simp
    _ ≤ ‖U‖ * (‖T‖ * ‖V‖) :=
      (U.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (T.opNorm_comp_le V) (norm_nonneg _))
    _ = _ := by ring

private theorem identity_factorization_norms_pos (T : E →L[𝕜] F)
    (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (h : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z) : 0 < ‖U‖ ∧ 0 < ‖V‖ := by
  have hb := identity_factorization_norm_bound T U V h
  constructor
  · by_contra hn
    have hz := le_antisymm (not_lt.mp hn) (norm_nonneg U)
    rw [hz, zero_mul, zero_mul] at hb
    norm_num at hb
  · by_contra hn
    have hz := le_antisymm (not_lt.mp hn) (norm_nonneg V)
    rw [hz, mul_zero] at hb
    norm_num at hb

theorem factorization_constant_le_norm (T : E →L[𝕜] F)
    (U : F →L[𝕜] Z) (V : Z →L[𝕜] E)
    (h : U.comp (T.comp V) = ContinuousLinearMap.id 𝕜 Z) :
    ‖U‖⁻¹ * ‖V‖⁻¹ ≤ ‖T‖ := by
  obtain ⟨hU, hV⟩ := identity_factorization_norms_pos T U V h
  have hb := identity_factorization_norm_bound T U V h
  have hdiv : 1 / (‖U‖ * ‖V‖) ≤ ‖T‖ :=
    (div_le_iff₀ (mul_pos hU hV)).mpr (by nlinarith)
  simpa only [one_div, mul_inv_rev, mul_comm] using hdiv

theorem factorizationSup_le_norm (T : E →L[𝕜] F) : factorizationSup Z T ≤ ‖T‖ := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, h, rfl⟩)
  · exact norm_nonneg T
  · exact factorization_constant_le_norm T U V h

theorem factorizationSup_nonneg (T : E →L[𝕜] F) : 0 ≤ factorizationSup Z T := by
  apply le_csSup
  · refine ⟨‖T‖, ?_⟩
    rintro r (rfl | ⟨U, V, h, rfl⟩)
    · exact norm_nonneg T
    · exact factorization_constant_le_norm T U V h
  · exact Set.mem_insert 0 _

/-- The actual factors through `A ∘ T ∘ B` compose to factors through `T`,
with at least as large a reciprocal norm product when `A` and `B` contract. -/
theorem factorizationSup_of_contractive_composition_le
    (T : E →L[𝕜] F) (A : F →L[𝕜] G) (B : H →L[𝕜] E)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    factorizationSup Z (A.comp (T.comp B)) ≤ factorizationSup Z T := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro r (rfl | ⟨U, V, h, rfl⟩)
  · exact factorizationSup_nonneg T
  · have hfact : (U.comp A).comp (T.comp (B.comp V)) = ContinuousLinearMap.id 𝕜 Z := by
      simpa only [ContinuousLinearMap.comp_assoc] using h
    obtain ⟨hUA, hBV⟩ := identity_factorization_norms_pos T (U.comp A) (B.comp V) hfact
    have hUnorm : ‖U.comp A‖ ≤ ‖U‖ :=
      (U.opNorm_comp_le A).trans (mul_le_of_le_one_right (norm_nonneg _) hA)
    have hVnorm : ‖B.comp V‖ ≤ ‖V‖ :=
      (B.opNorm_comp_le V).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
    have hconst : ‖U‖⁻¹ * ‖V‖⁻¹ ≤ ‖U.comp A‖⁻¹ * ‖B.comp V‖⁻¹ :=
      mul_le_mul (inv_anti₀ hUA hUnorm) (inv_anti₀ hBV hVnorm)
        (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (norm_nonneg _))
    apply hconst.trans
    apply le_csSup
    · refine ⟨‖T‖, ?_⟩
      rintro r (rfl | ⟨U', V', h', rfl⟩)
      · exact norm_nonneg T
      · exact factorization_constant_le_norm T U' V' h'
    · exact Set.mem_insert_of_mem _ ⟨U.comp A, B.comp V, hfact, rfl⟩

/-- Scalar ℓ¹ version, with nontriviality supplied by its zeroth unit vector. -/
theorem factorizationSup_ellOne_of_contractive_composition_le
    (T : E →L[𝕜] F) (A : F →L[𝕜] G) (B : H →L[𝕜] E)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    factorizationSup (EllOne 𝕜) (A.comp (T.comp B)) ≤ factorizationSup (EllOne 𝕜) T := by
  letI : Nontrivial (EllOne 𝕜) := ⟨⟨lp.single 1 0 1, 0, by
    intro h
    have hc := congrArg (fun x : EllOne 𝕜 => x 0) h
    simpa using hc⟩⟩
  exact factorizationSup_of_contractive_composition_le T A B hA hB

end PEMS
