import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Finite scalar sequences, their coefficient mass, interval restrictions and
tail-to-tail spreads for the shift-generated Gowers--Maurey construction.
The pairing is bilinear: these are coefficients of linear functionals.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace ThesisCommon
namespace GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

abbrev C00 (𝕜 : Type*) [Zero 𝕜] := ℕ →₀ 𝕜

def toEllOne : C00 𝕜 →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) 1 :=
  Finsupp.lsum 𝕜 (fun n => lp.lsingle (𝕜 := 𝕜) (E := fun _ : ℕ => 𝕜) 1 n)

@[simp] theorem toEllOne_apply (x : C00 𝕜) (n : ℕ) : toEllOne x n = x n := by
  classical
  simp [toEllOne, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_single,
    Pi.single_apply, Finsupp.mem_support_iff, eq_comm]

def mass : Seminorm 𝕜 (C00 𝕜) := (normSeminorm 𝕜 _).comp toEllOne

theorem mass_eq (x : C00 𝕜) : mass x = ∑ n ∈ x.support, ‖x n‖ := by
  classical
  have h := lp.norm_sum_single (E := fun _ : ℕ => 𝕜) (p := 1) (by simp) x x.support
  simpa [mass, toEllOne, Finsupp.lsum_apply, Finsupp.sum] using h

@[simp] theorem mass_single (n : ℕ) (c : 𝕜) : mass (Finsupp.single n c) = ‖c‖ := by
  classical
  simp [mass, toEllOne, Finsupp.lsum_apply]

theorem coordinate_le_mass (x : C00 𝕜) (n : ℕ) : ‖x n‖ ≤ mass x := by
  simpa only [toEllOne_apply] using
    lp.norm_apply_le_norm (by simp : (1 : ℝ≥0∞) ≠ 0) (toEllOne x) n

theorem seminorm_sum_le {ι : Type*} (q : Seminorm 𝕜 (C00 𝕜))
    (s : Finset ι) (x : ι → C00 𝕜) : q (∑ i ∈ s, x i) ≤ ∑ i ∈ s, q (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (map_add_le_add q _ _).trans (add_le_add_left ih _)

/-- Checking a seminorm on the scalar coordinate vectors bounds it by ℓ1 mass. -/
theorem seminorm_le_mass (q : Seminorm 𝕜 (C00 𝕜))
    (h : ∀ n c, q (Finsupp.single n c) ≤ ‖c‖) : q ≤ mass := by
  intro x
  change q x ≤ mass x
  rw [mass_eq]
  conv_lhs => rw [← Finsupp.sum_single x]
  change q (∑ n ∈ x.support, Finsupp.single n (x n)) ≤ _
  exact (seminorm_sum_le q _ _).trans (Finset.sum_le_sum fun n _ => h n (x n))

def coordinateSeminorm (n : ℕ) : Seminorm 𝕜 (C00 𝕜) :=
  (normSeminorm 𝕜 𝕜).comp (Finsupp.lapply n)

@[simp] theorem coordinateSeminorm_apply (n : ℕ) (x : C00 𝕜) :
    coordinateSeminorm n x = ‖x n‖ := rfl

theorem coordinateSeminorm_le_mass (n : ℕ) : coordinateSeminorm (𝕜 := 𝕜) n ≤ mass :=
  fun x => coordinate_le_mass x n

/-- A finite closed integer interval. Empty intervals are allowed. -/
structure Interval where
  first : ℕ
  last : ℕ
  deriving DecidableEq

def Interval.set (E : Interval) : Finset ℕ := Finset.Icc E.first E.last

def restrict (E : Interval) : C00 𝕜 →ₗ[𝕜] C00 𝕜 where
  toFun x := x.filter (· ∈ E.set)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp] theorem restrict_single (E : Interval) (n : ℕ) (c : 𝕜) :
    restrict E (Finsupp.single n c) = if n ∈ E.set then Finsupp.single n c else 0 := by
  classical
  change (Finsupp.single n c).filter (· ∈ E.set) = _
  split_ifs with hn
  · exact Finsupp.filter_single_of_pos (· ∈ E.set) hn
  · exact Finsupp.filter_single_of_neg (· ∈ E.set) hn

@[simp] theorem restrict_apply (E : Interval) (x : C00 𝕜) (n : ℕ) :
    restrict E x n = if n ∈ E.set then x n else 0 := by
  rfl

/-- The spread taking the tail starting at m onto the tail starting at n.
In the source's notation these are exactly S^n L^m (with zero-based indices). -/
def spread (m n : ℕ) : C00 𝕜 →ₗ[𝕜] C00 𝕜 :=
  Finsupp.lsum 𝕜 (fun i => if m ≤ i then Finsupp.lsingle (i - m + n) else 0)

@[simp] theorem spread_single (m n i : ℕ) (c : 𝕜) :
    spread m n (Finsupp.single i c) =
      if m ≤ i then Finsupp.single (i - m + n) c else 0 := by
  classical
  simp [spread, Finsupp.lsum_apply]
  split_ifs <;> rfl

theorem mass_spread_le (m n : ℕ) : (mass (𝕜 := 𝕜)).comp (spread m n) ≤ mass := by
  apply seminorm_le_mass
  intro i c
  simp only [Seminorm.comp_apply, spread_single]
  split_ifs <;> simp

def pairing (a : C00 𝕜) : C00 𝕜 →ₗ[𝕜] 𝕜 :=
  Finsupp.lsum 𝕜 (fun n => a n • LinearMap.id)

@[simp] theorem pairing_single (a : C00 𝕜) (n : ℕ) (c : 𝕜) :
    pairing a (Finsupp.single n c) = a n * c := by
  simp [pairing, Finsupp.lsum_apply]

def evaluationSeminorm (a : C00 𝕜) : Seminorm 𝕜 (C00 𝕜) :=
  (normSeminorm 𝕜 𝕜).comp (pairing a)

/-- The function f fixed throughout the Gowers--Maurey paper. -/
def logarithmicWeight (t : ℝ) : ℝ := Real.log (t + 1) / Real.log 2

theorem logarithmicWeight_one : logarithmicWeight 1 = 1 := by
  norm_num [logarithmicWeight, Real.log_ne_zero]

end GowersMaurey
end ThesisCommon
