import BanachIsometric.CompactFiberNeighborhoods
import BanachIsometric.LocalSignedIndex
import BanachIsometric.PiolaBoxFrontier
import BanachIsometric.SignedCountFiniteAdditivity
import BanachIsometric.SignedCountExcision

/-!
# Actual closed coordinate boxes around the finite roots

The ordinary Pi norm identifies coordinate boxes with closed metric balls.
Disjoint balls indexed by the entire actual fiber each contain precisely their
own root. Their actual coordinate-face boundaries therefore avoid the target.
-/

namespace BanachIsometric

open MeasureTheory Set Metric
open scoped Topology NNReal BigOperators

noncomputable section

theorem closedBall_piola_eq_Icc {n : ℕ} (x : PiolaSpace n) (s : ℝ) (hs : 0 ≤ s) :
    closedBall x s = Icc (x - s • (1 : PiolaSpace n)) (x + s • 1) := by
  rw [closedBall_pi x hs]
  ext z
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Real.closedBall_eq_Icc, Set.mem_Icc,
    Pi.le_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
    forall_and]

theorem piola_centeredBox_lower_le_upper {n : ℕ} (x : PiolaSpace n) {s : ℝ} (hs : 0 ≤ s) :
    x - s • (1 : PiolaSpace n) ≤ x + s • 1 := by
  intro i
  change x i - s * 1 ≤ x i + s * 1
  linarith

theorem root_mem_interior_of_avoids_boxBoundary {n : ℕ}
    (f : PiolaSpace n → PiolaSpace n) (a b c : PiolaSpace n)
    (hc : c ∉ f '' piolaBoxBoundary a b)
    (x : {x : PiolaSpace n // x ∈ Icc a b ∧ f x = c}) : x.val ∈ interior (Icc a b) := by
  by_contra hnot
  apply hc
  refine ⟨x.val, ?_, x.property.2⟩
  rw [piolaBoxBoundary_eq_frontier, frontier, isClosed_Icc.closure_eq]
  exact ⟨x.property.1, hnot⟩

theorem unique_root_of_disjoint_fiber_balls {n : ℕ}
    (f : PiolaSpace n → PiolaSpace n) (S : Set (PiolaSpace n)) (c : PiolaSpace n)
    (s : {x : PiolaSpace n // x ∈ S ∧ f x = c} → ℝ)
    (hs : ∀ x, 0 ≤ s x) (hsub : ∀ x, closedBall x.val (s x) ⊆ S)
    (hdis : Pairwise (fun x y => Disjoint (closedBall x.val (s x)) (closedBall y.val (s y))))
    (x : {x : PiolaSpace n // x ∈ S ∧ f x = c}) (z : PiolaSpace n)
    (hz : z ∈ closedBall x.val (s x)) (hzc : f z = c) : z = x.val := by
  let y : {x : PiolaSpace n // x ∈ S ∧ f x = c} := ⟨z, hsub x hz, hzc⟩
  have hxy : x = y := by
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) hz (mem_closedBall_self (hs y))
  exact (congrArg Subtype.val hxy).symm

theorem root_ball_boundary_avoids_target {n : ℕ}
    (f : PiolaSpace n → PiolaSpace n) (S : Set (PiolaSpace n)) (c : PiolaSpace n)
    (s : {x : PiolaSpace n // x ∈ S ∧ f x = c} → ℝ)
    (hs : ∀ x, 0 < s x) (hsub : ∀ x, closedBall x.val (s x) ⊆ S)
    (hdis : Pairwise (fun x y => Disjoint (closedBall x.val (s x)) (closedBall y.val (s y))))
    (x : {x : PiolaSpace n // x ∈ S ∧ f x = c}) :
    c ∉ f '' piolaBoxBoundary (x.val - s x • (1 : PiolaSpace n)) (x.val + s x • 1) := by
  rintro ⟨z, hz, hzc⟩
  rw [piolaBoxBoundary_eq_frontier, ← closedBall_piola_eq_Icc _ _ (hs x).le] at hz
  have hzball : z ∈ closedBall x.val (s x) := by
    simpa only [isClosed_closedBall.closure_eq] using hz.1
  have hzx := unique_root_of_disjoint_fiber_balls f S c s (fun y => (hs y).le) hsub hdis x z hzball hzc
  have hxint : x.val ∈ interior (closedBall x.val (s x)) :=
    ball_subset_interior_closedBall (mem_ball_self (hs x))
  exact hz.2 (hzx.symm ▸ hxint)

end

end BanachIsometric
