import Posets.AlspachCounterexampleEvaluation

/-! The first family in Alspach's construction: the distinguished row is
δ_p and every other row is (δ_x + δ_p)/2. This is already a concrete
continuous family with the uniform ℓ¹ lower estimate and onto evaluation. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open JLMS
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜]

def alspachBaseRow (p x : K) : AlspachProbability K :=
  if x = p then .point p else .average (.point x) (.point p)

def alspachBaseForest (p : K) : AlspachForestRows 𝕜 K (lp (fun _ : K => 𝕜) 1) :=
  alspachForestOfProbabilities
    (fun x => if x = p then none else some p)
    (fun x => if x = p then 0 else 1)
    (by
      intro i j hij
      by_cases hi : i = p
      · simp [hi] at hij
      · simp only [hi, ↓reduceIte, Option.some.injEq] at hij
        subst j
        simp [hi])
    (fun x => .point x) (alspachBaseRow p) (fun x => some x)
    (by intro i k hk; simpa only [AlspachProbability.support, Finset.mem_singleton, Option.some.injEq] using hk)
    (by
      intro i hi
      by_cases hip : i = p
      · subst i; simp [alspachBaseRow]
      · simp [hip] at hi)
    (by
      intro i j hij
      by_cases hip : i = p
      · simp [hip] at hij
      · simp only [hip, ↓reduceIte, Option.some.injEq] at hij
        subst j
        simp [alspachBaseRow, hip])

variable [TopologicalSpace K]

theorem alspachBaseRow_apply (M : AtomicDualModel 𝕜 K) (p x : K) (f : CZero 𝕜 K) :
    M.representation.symm ((alspachBaseRow p x).vector) f =
      (1 / 2 : 𝕜) * (f x + f p) := by
  by_cases hxp : x = p
  · subst x
    simp only [alspachBaseRow, ↓reduceIte, AlspachProbability.vector, M.pointMass,
      evaluation_apply]
    ring
  · simp only [alspachBaseRow, hxp, ↓reduceIte, AlspachProbability.vector,
      map_smul, map_add, M.pointMass, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, evaluation_apply, smul_eq_mul]

theorem alspachBaseRow_continuous (M : AtomicDualModel 𝕜 K) (p : K) (f : CZero 𝕜 K) :
    Continuous (fun x => M.representation.symm ((alspachBaseForest (𝕜 := 𝕜) p).row x) f) := by
  change Continuous (fun x => M.representation.symm ((alspachBaseRow p x).vector) f)
  simp_rw [alspachBaseRow_apply]
  exact continuous_const.mul (f.continuous.add continuous_const)

theorem alspachBaseEvaluation_surjective [CompactSpace K] (M : AtomicDualModel 𝕜 K) (p : K) :
    Function.Surjective (alspachEvaluation
      (fun x => M.representation.symm ((alspachBaseForest (𝕜 := 𝕜) p).row x))
      (alspachBaseRow_continuous M p)
      (fun x => by simpa only [M.representation.symm.norm_map] using
        (alspachBaseForest (𝕜 := 𝕜) p).row_norm_le x)) :=
  alspachForestEvaluation_surjective M M (alspachBaseForest p) (alspachBaseRow_continuous M p)

end Posets

