import ThesisCommon.Combinatorics.OrderedTuples
import Mathlib.Data.Real.Basic

/-! The eight ordered off-diagonal patterns in finite matrix scalarisation.
A homogeneous bad pattern contradicts a good source-coordinate slice. -/
noncomputable section
namespace ThesisCommon

def MatrixGoodSlices (w : ℕ → ℕ → ℕ → ℕ → ℝ) (δ : ℝ) (m : ℕ) (S : Set ℕ) : Prop :=
  (∀ j ∈ S, ∀ k ∈ S, ∀ l ∈ S, ∀ g : Fin m ↪o ℕ,
    Set.range g ⊆ S → ∃ r, w (g r) j k l < δ) ∧
  (∀ i ∈ S, ∀ k ∈ S, ∀ l ∈ S, ∀ g : Fin m ↪o ℕ,
    Set.range g ⊆ S → ∃ r, w i (g r) k l < δ)

def matrixTripleBadColor (w : ℕ → ℕ → ℕ → ℕ → ℝ) (δ : ℝ)
    (e : Fin 3 ↪o ℕ) : Fin 4 → Bool := by
  classical
  exact ![decide (δ ≤ w (e 0) (e 1) (e 0) (e 2)),
    decide (δ ≤ w (e 0) (e 2) (e 0) (e 1)),
    decide (δ ≤ w (e 0) (e 2) (e 1) (e 2)),
    decide (δ ≤ w (e 1) (e 2) (e 0) (e 2))]

def matrixQuadrupleBadColor (w : ℕ → ℕ → ℕ → ℕ → ℝ) (δ : ℝ)
    (e : Fin 4 ↪o ℕ) : Fin 4 → Bool := by
  classical
  exact ![decide (δ ≤ w (e 0) (e 2) (e 1) (e 3)),
    decide (δ ≤ w (e 0) (e 3) (e 1) (e 2)),
    decide (δ ≤ w (e 1) (e 2) (e 0) (e 3)),
    decide (δ ≤ w (e 1) (e 3) (e 0) (e 2))]

theorem matrix_homogeneous_bad_colors_false
    {w : ℕ → ℕ → ℕ → ℕ → ℝ} {δ : ℝ} {m L : ℕ} {S : Set ℕ}
    (hL : m + 3 ≤ L) (e : Fin L ↪o ℕ) (he : Set.range e ⊆ S)
    (hslices : MatrixGoodSlices w δ m S)
    {γ₃ γ₄ : Fin 4 → Bool}
    (h₃ : OrderedHomogeneous (matrixTripleBadColor w δ) S γ₃)
    (h₄ : OrderedHomogeneous (matrixQuadrupleBadColor w δ) S γ₄) :
    γ₃ = (fun _ => false) ∧ γ₄ = (fun _ => false) := by
  classical
  have hem (i : Fin L) : e i ∈ S := he ⟨i, rfl⟩
  have hwin (o : ℕ) (ho : o + m ≤ L) :
      Set.range (orderedWindow e o ho) ⊆ S := by
    rintro _ ⟨i, rfl⟩
    exact hem _
  let a : Fin L := ⟨0, by omega⟩
  let b : Fin L := ⟨1, by omega⟩
  let c : Fin L := ⟨m, by omega⟩
  let d : Fin L := ⟨m + 1, by omega⟩
  let f : Fin L := ⟨m + 2, by omega⟩
  have alt (r : Fin m) : e a < orderedWindow e 1 (by omega) r := by
    apply e.strictMono
    change 0 < 1 + r.val
    omega
  have wlt (r : Fin m) : orderedWindow e 1 (by omega) r < e d := by
    apply e.strictMono
    change 1 + r.val < m + 1
    omega
  have clt (r : Fin m) : orderedWindow e 0 (by omega) r < e c := by
    apply e.strictMono
    change 0 + r.val < m
    omega
  have ab : e a < e b := e.strictMono (by change 0 < 1; omega)
  have cd : e c < e d := e.strictMono (by change m < m + 1; omega)
  have df : e d < e f := e.strictMono (by change m + 1 < m + 2; omega)
  constructor
  · funext t
    fin_cases t
    · obtain ⟨r, hr⟩ := hslices.2 (e a) (hem _) (e a) (hem _) (e d) (hem _)
        (orderedWindow e 1 (by omega)) (hwin 1 (by omega))
      simp only [orderedWindow_apply] at hr
      have hh := congrFun (h₃ (orderedTriple (e a) (orderedWindow e 1 (by omega) r) (e d) (alt r) (wlt r)) (range_orderedTriple_subset (alt r) (wlt r) (hem _) (hem _) (hem _))) 0
      simpa [matrixTripleBadColor, orderedTriple, not_le.mpr hr] using hh.symm
    · obtain ⟨r, hr⟩ := hslices.2 (e a) (hem _) (e a) (hem _) (e b) (hem _)
        (orderedWindow e 2 (by omega)) (hwin 2 (by omega))
      have blt : e b < orderedWindow e 2 (by omega) r := by
        apply e.strictMono
        change 1 < 2 + r.val
        omega
      simp only [orderedWindow_apply] at hr
      have hh := congrFun (h₃ (orderedTriple (e a) (e b) (orderedWindow e 2 (by omega) r) ab blt) (range_orderedTriple_subset ab blt (hem _) (hem _) (hem _))) 1
      simpa [matrixTripleBadColor, orderedTriple, not_le.mpr hr] using hh.symm
    · obtain ⟨r, hr⟩ := hslices.1 (e d) (hem _) (e c) (hem _) (e d) (hem _)
        (orderedWindow e 0 (by omega)) (hwin 0 (by omega))
      simp only [orderedWindow_apply, zero_add] at hr
      have hh := congrFun (h₃ (orderedTriple (orderedWindow e 0 (by omega) r) (e c) (e d) (clt r) cd) (range_orderedTriple_subset (clt r) cd (hem _) (hem _) (hem _))) 2
      simpa [matrixTripleBadColor, orderedTriple, not_le.mpr hr] using hh.symm
    · obtain ⟨r, hr⟩ := hslices.1 (e d) (hem _) (e a) (hem _) (e d) (hem _)
        (orderedWindow e 1 (by omega)) (hwin 1 (by omega))
      simp only [orderedWindow_apply] at hr
      have hh := congrFun (h₃ (orderedTriple (e a) (orderedWindow e 1 (by omega) r) (e d) (alt r) (wlt r)) (range_orderedTriple_subset (alt r) (wlt r) (hem _) (hem _) (hem _))) 3
      simpa [matrixTripleBadColor, orderedTriple, not_le.mpr hr] using hh.symm
  · funext t
    fin_cases t
    · obtain ⟨r, hr⟩ := hslices.1 (e d) (hem _) (e c) (hem _) (e f) (hem _)
        (orderedWindow e 0 (by omega)) (hwin 0 (by omega))
      simp only [orderedWindow_apply, zero_add] at hr
      have hh := congrFun (h₄ (orderedQuadruple (orderedWindow e 0 (by omega) r) (e c) (e d) (e f) (clt r) cd df) (range_orderedQuadruple_subset (clt r) cd df (hem _) (hem _) (hem _) (hem _))) 0
      simpa [matrixQuadrupleBadColor, orderedQuadruple, not_le.mpr hr] using hh.symm
    · obtain ⟨r, hr⟩ := hslices.1 (e f) (hem _) (e c) (hem _) (e d) (hem _)
        (orderedWindow e 0 (by omega)) (hwin 0 (by omega))
      simp only [orderedWindow_apply, zero_add] at hr
      have hh := congrFun (h₄ (orderedQuadruple (orderedWindow e 0 (by omega) r) (e c) (e d) (e f) (clt r) cd df) (range_orderedQuadruple_subset (clt r) cd df (hem _) (hem _) (hem _) (hem _))) 1
      simpa [matrixQuadrupleBadColor, orderedQuadruple, not_le.mpr hr] using hh.symm
    · obtain ⟨r, hr⟩ := hslices.1 (e d) (hem _) (e a) (hem _) (e f) (hem _)
        (orderedWindow e 1 (by omega)) (hwin 1 (by omega))
      simp only [orderedWindow_apply] at hr
      have hh := congrFun (h₄ (orderedQuadruple (e a) (orderedWindow e 1 (by omega) r) (e d) (e f) (alt r) (wlt r) df) (range_orderedQuadruple_subset (alt r) (wlt r) df (hem _) (hem _) (hem _) (hem _))) 2
      simpa [matrixQuadrupleBadColor, orderedQuadruple, not_le.mpr hr] using hh.symm
    · obtain ⟨r, hr⟩ := hslices.1 (e f) (hem _) (e a) (hem _) (e d) (hem _)
        (orderedWindow e 1 (by omega)) (hwin 1 (by omega))
      simp only [orderedWindow_apply] at hr
      have hh := congrFun (h₄ (orderedQuadruple (e a) (orderedWindow e 1 (by omega) r) (e d) (e f) (alt r) (wlt r) df) (range_orderedQuadruple_subset (alt r) (wlt r) df (hem _) (hem _) (hem _) (hem _))) 3
      simpa [matrixQuadrupleBadColor, orderedQuadruple, not_le.mpr hr] using hh.symm

end ThesisCommon

