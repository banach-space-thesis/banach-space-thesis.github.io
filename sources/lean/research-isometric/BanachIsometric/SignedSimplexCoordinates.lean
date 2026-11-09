import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

/-! Oriented affine coordinates on the real standard simplex.
The coordinates are the barycentric weights after the first vertex, in their
original order. The product norm in this chart is used only for Lipschitz
estimates; the chart does not change a norm or scalar action of a target body. -/

noncomputable section
namespace BanachIsometric.SingularPrism

open Set
open scoped Topology NNReal

abbrev SignedCoordinateSimplex (n : ℕ) := ↥(stdSimplex ℝ (Fin (n + 1)))

def signedSimplexDomain (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def signedSimplexBarycentric (n : ℕ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (1 - ∑ i, x i) x

@[simp] theorem signedSimplexBarycentric_zero (n : ℕ) (x : Fin n → ℝ) :
    signedSimplexBarycentric n x 0 = 1 - ∑ i, x i := rfl

@[simp] theorem signedSimplexBarycentric_succ (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    signedSimplexBarycentric n x i.succ = x i := rfl

theorem signedSimplexBarycentric_mem (n : ℕ) {x : Fin n → ℝ}
    (hx : x ∈ signedSimplexDomain n) : signedSimplexBarycentric n x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact sub_nonneg.mpr hx.2
    · exact hx.1 j
  · rw [Fin.sum_univ_succ]
    simp

def signedSimplexDrop (n : ℕ) (s : SignedCoordinateSimplex n) : Fin n → ℝ := fun i => s i.succ

theorem signedSimplexDrop_mem (n : ℕ) (s : SignedCoordinateSimplex n) :
    signedSimplexDrop n s ∈ signedSimplexDomain n := by
  refine ⟨fun i => stdSimplex.zero_le s i.succ, ?_⟩
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  dsimp only [signedSimplexDrop]
  linarith [stdSimplex.zero_le s 0]

theorem signedSimplexBarycentric_drop (n : ℕ) (s : SignedCoordinateSimplex n) :
    signedSimplexBarycentric n (signedSimplexDrop n s) = s.val := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  change 1 - (∑ j : Fin n, s j.succ) = s 0
  linarith

theorem signedSimplexDrop_lipschitz (n : ℕ) : LipschitzWith 1 (signedSimplexDrop n) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  simpa only [signedSimplexDrop, Function.eval, NNReal.coe_one, one_mul] using
    (LipschitzWith.eval i.succ : LipschitzWith 1
      (Function.eval i.succ : (Fin (n + 1) → ℝ) → ℝ)).dist_le_mul s.val t.val

theorem signedSimplexBarycentric_lipschitz (n : ℕ) :
    LipschitzWith ((n : ℝ≥0) + 1) (signedSimplexBarycentric n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)]
  have hcoord (j : Fin n) : dist (x j) (y j) ≤ dist x y := by
    simpa using (LipschitzWith.eval j : LipschitzWith 1 (Function.eval j : (Fin n → ℝ) → ℝ)).dist_le_mul x y
  have hb : 0 ≤ dist x y := dist_nonneg
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [signedSimplexBarycentric_zero, signedSimplexBarycentric_zero, Real.dist_eq]
    have he : (1 - ∑ j, x j) - (1 - ∑ j, y j) = ∑ j, (y j - x j) := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [he]
    calc
      |∑ j, (y j - x j)| ≤ ∑ j, |y j - x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, dist x y := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [← Real.dist_eq, dist_comm (y j) (x j)] using hcoord j
      _ ≤ (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) * dist x y := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        linarith
  · rw [signedSimplexBarycentric_succ, signedSimplexBarycentric_succ]
    apply (hcoord j).trans
    apply le_mul_of_one_le_left hb
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]

def signedSimplexCoordinates (n : ℕ) : SignedCoordinateSimplex n ≃ₜ signedSimplexDomain n where
  toFun s := ⟨signedSimplexDrop n s, signedSimplexDrop_mem n s⟩
  invFun x := ⟨signedSimplexBarycentric n x.val, signedSimplexBarycentric_mem n x.property⟩
  left_inv s := Subtype.ext (signedSimplexBarycentric_drop n s)
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (signedSimplexDrop_lipschitz n).continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (signedSimplexBarycentric_lipschitz n).continuous.comp continuous_subtype_val

theorem signedSimplexCoordinates_lipschitz (n : ℕ) : LipschitzWith 1 (signedSimplexCoordinates n) :=
  (signedSimplexDrop_lipschitz n).subtype_mk _

theorem signedSimplexCoordinates_symm_lipschitz (n : ℕ) :
    LipschitzWith ((n : ℝ≥0) + 1) (signedSimplexCoordinates n).symm := by
  simpa only [mul_one] using (((signedSimplexBarycentric_lipschitz n).comp
    (LipschitzWith.subtype_val (signedSimplexDomain n))).subtype_mk
      (fun x => signedSimplexBarycentric_mem n x.property))

theorem isCompact_signedSimplexDomain (n : ℕ) : IsCompact (signedSimplexDomain n) := by
  have h : range (signedSimplexDrop n) = signedSimplexDomain n := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact signedSimplexDrop_mem n s
    · intro hx
      exact ⟨(signedSimplexCoordinates n).symm ⟨x, hx⟩, rfl⟩
  rw [← h]
  exact isCompact_range (signedSimplexDrop_lipschitz n).continuous

theorem mem_interior_signedSimplexDomain_of_pos (n : ℕ) {x : Fin n → ℝ}
    (hpos : ∀ j, 0 < x j) (hsum : ∑ j, x j < 1) : x ∈ interior (signedSimplexDomain n) := by
  let U : Set (Fin n → ℝ) := (⋂ j, {z | 0 < z j}) ∩ {z | ∑ j, z j < 1}
  have hU : IsOpen U := (isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const (continuous_apply j)).inter
      (isOpen_lt (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const)
  have hxU : x ∈ U := ⟨mem_iInter.mpr hpos, hsum⟩
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hxU) fun z hz =>
    ⟨fun j => (mem_iInter.mp hz.1 j).le, hz.2.le⟩)

end BanachIsometric.SingularPrism
