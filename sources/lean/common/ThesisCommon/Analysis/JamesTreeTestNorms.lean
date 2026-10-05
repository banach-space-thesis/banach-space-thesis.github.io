import ThesisCommon.Analysis.JamesTreeSegments
import ThesisCommon.Analysis.SequenceSpaces
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! Actual finite ℓp norms of disjoint segment sums on c₀₀ of the dyadic tree.
Every test is bounded by the finite coefficient ℓ1 mass: each node belongs
to at most one tested segment. This proves finiteness of the supremum norm
without imposing any extra membership hypothesis on c₀₀. -/
noncomputable section
open scoped ENNReal BigOperators
namespace ThesisCommon
variable (𝕜 : Type*) [RCLike 𝕜] (p : BanachExponent)
variable {S : JamesTreeSegmentFamily}

/-- The vector of segment sums, in its actual finite ℓp norm. -/
def jamesTreeTestMap (T : JamesTreeTest S) :
    (DyadicTreeNode →₀ 𝕜) →ₗ[𝕜] PiLp p.val (fun _ : Fin T.count => 𝕜) where
  toFun a := WithLp.toLp p.val (fun j => ∑ t ∈ T.segment j, a t)
  map_add' := by
    intro a b
    ext j
    change (∑ t ∈ T.segment j, (a + b) t) =
      (∑ t ∈ T.segment j, a t) + ∑ t ∈ T.segment j, b t
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    ext j
    change (∑ t ∈ T.segment j, (c • a) t) = c • ∑ t ∈ T.segment j, a t
    simp only [Finsupp.smul_apply, Finset.smul_sum]

@[simp] theorem jamesTreeTestMap_apply (T : JamesTreeTest S)
    (a : DyadicTreeNode →₀ 𝕜) (j : Fin T.count) :
    jamesTreeTestMap 𝕜 p T a j = ∑ t ∈ T.segment j, a t := rfl

@[simp] theorem jamesTreeTestMap_single_apply (T : JamesTreeTest S)
    (t : DyadicTreeNode) (c : 𝕜) (j : Fin T.count) :
    jamesTreeTestMap 𝕜 p T (Finsupp.single t c) j =
      if t ∈ T.segment j then c else 0 := by
  classical
  simp [jamesTreeTestMap_apply, Finsupp.single_apply]

/-- A coefficient contributes to at most one segment in any disjoint test. -/
theorem jamesTreeTestMap_single_norm_le (T : JamesTreeTest S)
    (t : DyadicTreeNode) (c : 𝕜) :
    ‖jamesTreeTestMap 𝕜 p T (Finsupp.single t c)‖ ≤ ‖c‖ := by
  classical
  by_cases hex : ∃ j, t ∈ T.segment j
  · obtain ⟨j, hj⟩ := hex
    have heq : jamesTreeTestMap 𝕜 p T (Finsupp.single t c) =
        WithLp.toLp p.val (Pi.single j c) := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [Finsupp.single_apply, hj]
      · have hi : t ∉ T.segment i := by
          intro hit
          exact Finset.disjoint_left.mp (T.disjoint hij) hit hj
        simp [Finsupp.single_apply, hi, hij]
    rw [heq, PiLp.norm_toLp_single]
  · have heq : jamesTreeTestMap 𝕜 p T (Finsupp.single t c) = 0 := by
      ext i
      have hi : t ∉ T.segment i := fun hi => hex ⟨i, hi⟩
      simp [Finsupp.single_apply, hi]
    rw [heq, norm_zero]
    exact norm_nonneg c

/-- Uniform finite ℓ1 bound for every segment test of a finitely supported vector. -/
theorem jamesTreeTestMap_norm_le_mass (T : JamesTreeTest S) (a : DyadicTreeNode →₀ 𝕜) :
    ‖jamesTreeTestMap 𝕜 p T a‖ ≤ ∑ t ∈ a.support, ‖a t‖ := by
  classical
  have hsum : (∑ t ∈ a.support, Finsupp.single t (a t)) = a := Finsupp.sum_single a
  calc
    _ = ‖jamesTreeTestMap 𝕜 p T (∑ t ∈ a.support, Finsupp.single t (a t))‖ :=
      congrArg (fun b => ‖jamesTreeTestMap 𝕜 p T b‖) hsum.symm
    _ = ‖∑ t ∈ a.support, jamesTreeTestMap 𝕜 p T (Finsupp.single t (a t))‖ := by
      rw [map_sum]
    _ ≤ ∑ t ∈ a.support, ‖jamesTreeTestMap 𝕜 p T (Finsupp.single t (a t))‖ :=
      norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun t _ => jamesTreeTestMap_single_norm_le 𝕜 p T t (a t)

theorem jamesTree_singleton_coordinate_le (S : JamesTreeSegmentFamily)
    (a : DyadicTreeNode →₀ 𝕜) (t : DyadicTreeNode) :
    ‖a t‖ ≤ ‖jamesTreeTestMap 𝕜 p (JamesTreeTest.singleton S t) a‖ := by
  have h := PiLp.norm_apply_le
    (jamesTreeTestMap 𝕜 p (JamesTreeTest.singleton S t) a) (0 : Fin 1)
  change ‖∑ u ∈ ({t} : Finset DyadicTreeNode), a u‖ ≤
    ‖jamesTreeTestMap 𝕜 p (JamesTreeTest.singleton S t) a‖ at h
  simpa only [Finset.sum_singleton] using h

/-- The exact finite-p test expression printed in the manuscript. -/
theorem jamesTreeTestMap_norm (hp : p.val ≠ ∞)
    (T : JamesTreeTest S) (a : DyadicTreeNode →₀ 𝕜) :
    ‖jamesTreeTestMap 𝕜 p T a‖ =
      (∑ j : Fin T.count, ‖∑ t ∈ T.segment j, a t‖ ^ p.val.toReal) ^
        (1 / p.val.toReal) := by
  exact PiLp.norm_eq_sum
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le p.property)) hp) _

end ThesisCommon
