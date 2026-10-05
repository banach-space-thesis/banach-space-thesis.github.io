import PEMS.ContinuousMapCZeroFixing
import PEMS.CZeroFactorizationClauses

/-! All three clauses of Theorem 1.5, for actual compact Hausdorff spaces
over both scalar fields. Disjoint regular-measure witnesses, complemented
c0 subcopies and exact infinity extensions are constructed in the dependencies. -/
noncomputable section
namespace PEMS
variable {K L : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

theorem theorem_1_5_real (T : C(L, ℝ) →L[ℝ] C(K, ℝ)) : Theorem_1_5 K L T :=
  theorem_1_5_of_fixing_formula T (dualWeakEssentialNorm_eq_fixesCZeroSup_real T)

theorem theorem_1_5_complex (T : C(L, ℂ) →L[ℂ] C(K, ℂ)) : Theorem_1_5 K L T :=
  theorem_1_5_of_fixing_formula T (dualWeakEssentialNorm_eq_fixesCZeroSup_complex T)

end PEMS
