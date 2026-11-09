import LindenstraussRetraction.SchauderBasis
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Flattening consecutive finite blocks

A uniformly bounded family of partial block projections, with compatible
successive blocks and convergent complete block projections, gives a sequential
Schauder basis. The enumeration visits every coordinate of one block before
starting the next block; it does not impose unconditional convergence.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace LindenstraussRetraction

universe u v

/-- The position of a coordinate in a sequence of finite blocks. -/
abbrev BlockPosition (d : ℕ → ℕ) := (b : ℕ) × Fin (d b)

/-- The number of coordinates preceding block `b`. -/
def blockOffset (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => blockOffset d b + d b

@[simp] theorem blockOffset_zero (d : ℕ → ℕ) : blockOffset d 0 = 0 := rfl

@[simp] theorem blockOffset_succ (d : ℕ → ℕ) (b : ℕ) :
    blockOffset d (b + 1) = blockOffset d b + d b := rfl

theorem blockOffset_eq_sum (d : ℕ → ℕ) (b : ℕ) :
    blockOffset d b = ∑ a ∈ Finset.range b, d a := by
  induction b with
  | zero => simp
  | succ b ih => simp only [blockOffset_succ, Finset.sum_range_succ, ih]

theorem blockOffset_strictMono {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) :
    StrictMono (blockOffset d) :=
  strictMono_nat_of_lt_succ fun b => by
    have hb := hd b
    simp only [blockOffset_succ]
    omega

/-- Encode a block position by its consecutive natural-number index. -/
def blockEncode {d : ℕ → ℕ} (p : BlockPosition d) : ℕ :=
  blockOffset d p.1 + p.2.val

theorem blockEncode_injective {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) :
    Function.Injective (@blockEncode d) := by
  rintro ⟨b, i⟩ ⟨c, j⟩ he
  have hm := (blockOffset_strictMono hd).monotone
  have hbc : b = c := by
    rcases lt_trichotomy b c with h | h | h
    · have hle := hm (Nat.succ_le_of_lt h)
      simp only [blockOffset_succ] at hle
      have hi := i.isLt
      change blockOffset d b + i.val = blockOffset d c + j.val at he
      omega
    · exact h
    · have hle := hm (Nat.succ_le_of_lt h)
      simp only [blockOffset_succ] at hle
      have hj := j.isLt
      change blockOffset d b + i.val = blockOffset d c + j.val at he
      omega
  subst c
  have hij : i = j := Fin.ext (by
    change blockOffset d b + i.val = blockOffset d b + j.val at he
    omega)
  subst j
  rfl

/-- First coordinate of the first nonempty block. -/
def blockFirst {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) : BlockPosition d :=
  ⟨0, ⟨0, hd 0⟩⟩

/-- Increment within a block, or start the next block. -/
def blockNext {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) (p : BlockPosition d) :
    BlockPosition d :=
  if h : p.2.val + 1 < d p.1 then
    ⟨p.1, ⟨p.2.val + 1, h⟩⟩
  else ⟨p.1 + 1, ⟨0, hd (p.1 + 1)⟩⟩

@[simp] theorem blockEncode_first {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) :
    blockEncode (blockFirst hd) = 0 := rfl

@[simp] theorem blockEncode_next {d : ℕ → ℕ} (hd : ∀ b, 0 < d b)
    (p : BlockPosition d) : blockEncode (blockNext hd p) = blockEncode p + 1 := by
  rcases p with ⟨b, i⟩
  unfold blockNext
  split_ifs with h
  · simp only [blockEncode]
    omega
  · simp only [blockEncode, blockOffset_succ, Nat.add_zero]
    change ¬ i.val + 1 < d b at h
    have hi := i.isLt
    omega

/-- Consecutive enumeration of all finite-block coordinates. -/
def blockEnumeration {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) : ℕ → BlockPosition d
  | 0 => blockFirst hd
  | n + 1 => blockNext hd (blockEnumeration hd n)

@[simp] theorem blockEncode_enumeration {d : ℕ → ℕ} (hd : ∀ b, 0 < d b)
    (n : ℕ) : blockEncode (blockEnumeration hd n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [blockEnumeration, blockEncode_next, ih]

@[simp] theorem blockEnumeration_encode {d : ℕ → ℕ} (hd : ∀ b, 0 < d b)
    (p : BlockPosition d) : blockEnumeration hd (blockEncode p) = p :=
  blockEncode_injective hd (blockEncode_enumeration hd (blockEncode p))

/-- The ordered finite-block coordinate set is equivalent to `ℕ`. -/
def blockEnumerationEquiv {d : ℕ → ℕ} (hd : ∀ b, 0 < d b) : ℕ ≃ BlockPosition d where
  toFun := blockEnumeration hd
  invFun := blockEncode
  left_inv := blockEncode_enumeration hd
  right_inv := blockEnumeration_encode hd

variable (𝕜 : Type v) [RCLike 𝕜]
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Finite block coordinates and compatible partial-block projections.
The bound `3` is the bound used for the auxiliary space in the paper. -/
structure BlockBasisData where
  size : ℕ → ℕ
  size_pos : ∀ b, 0 < size b
  vector : ∀ b, Fin (size b) → X
  coord : ∀ b, Fin (size b) → X →L[𝕜] 𝕜
  biorthogonal : ∀ (p q : BlockPosition size),
    coord p.1 p.2 (vector q.1 q.2) = if p = q then 1 else 0
  projection : ℕ → ℕ → X →L[𝕜] X
  projection_zero : projection 0 0 = 0
  projection_boundary : ∀ b, projection b (size b) = projection (b + 1) 0
  projection_step : ∀ b (i : Fin (size b)),
    projection b (i.val + 1) = projection b i.val + (coord b i).smulRight (vector b i)
  projection_bound : ∀ b r, r ≤ size b → ‖projection b r‖ ≤ 3
  full_tendsto : ∀ x : X, Tendsto (fun b => projection b 0 x) atTop (𝓝 x)

namespace BlockBasisData

variable {𝕜 X}

def flatVector (D : BlockBasisData 𝕜 X) (n : ℕ) : X :=
  let p := blockEnumeration D.size_pos n
  D.vector p.1 p.2

def flatCoord (D : BlockBasisData 𝕜 X) (n : ℕ) : X →L[𝕜] 𝕜 :=
  let p := blockEnumeration D.size_pos n
  D.coord p.1 p.2

def flatProjection (D : BlockBasisData 𝕜 X) (n : ℕ) : X →L[𝕜] X :=
  let p := blockEnumeration D.size_pos n
  D.projection p.1 p.2.val

@[simp] theorem flatVector_blockEncode (D : BlockBasisData 𝕜 X) (p : BlockPosition D.size) :
    D.flatVector (blockEncode p) = D.vector p.1 p.2 := by
  unfold flatVector
  rw [blockEnumeration_encode D.size_pos p]

@[simp] theorem flatCoord_blockEncode (D : BlockBasisData 𝕜 X) (p : BlockPosition D.size) :
    D.flatCoord (blockEncode p) = D.coord p.1 p.2 := by
  unfold flatCoord
  rw [blockEnumeration_encode D.size_pos p]

theorem flat_biorthogonal (D : BlockBasisData 𝕜 X) (n m : ℕ) :
    D.flatCoord n (D.flatVector m) = if n = m then 1 else 0 := by
  change D.coord _ _ (D.vector _ _) = _
  rw [D.biorthogonal]
  change (if (blockEnumerationEquiv D.size_pos) n =
    (blockEnumerationEquiv D.size_pos) m then 1 else 0) = _
  simp only [Equiv.apply_eq_iff_eq]

@[simp] theorem flatProjection_zero (D : BlockBasisData 𝕜 X) :
    D.flatProjection 0 = 0 := D.projection_zero

theorem flatProjection_succ (D : BlockBasisData 𝕜 X) (n : ℕ) :
    D.flatProjection (n + 1) = D.flatProjection n +
      (D.flatCoord n).smulRight (D.flatVector n) := by
  simp only [flatProjection, flatCoord, flatVector]
  change D.projection (blockNext D.size_pos (blockEnumeration D.size_pos n)).1
    (blockNext D.size_pos (blockEnumeration D.size_pos n)).2.val = _
  generalize blockEnumeration D.size_pos n = p
  rcases p with ⟨b, i⟩
  change D.projection (blockNext D.size_pos ⟨b, i⟩).1
    (blockNext D.size_pos ⟨b, i⟩).2.val =
    D.projection b i.val + (D.coord b i).smulRight (D.vector b i)
  by_cases h : i.val + 1 < D.size b
  · have hnext : blockNext D.size_pos (⟨b, i⟩ : BlockPosition D.size) =
        ⟨b, ⟨i.val + 1, h⟩⟩ := by
      unfold blockNext
      exact dif_pos h
    rw [hnext]
    exact D.projection_step b i
  · have hnext : blockNext D.size_pos (⟨b, i⟩ : BlockPosition D.size) =
        ⟨b + 1, ⟨0, D.size_pos (b + 1)⟩⟩ := by
      unfold blockNext
      exact dif_neg h
    rw [hnext]
    change D.projection (b + 1) 0 = _
    have hi := i.isLt
    change ¬ i.val + 1 < D.size b at h
    have he : i.val + 1 = D.size b := by omega
    exact (D.projection_boundary b).symm.trans
      ((congrArg (D.projection b) he.symm).trans (D.projection_step b i))

def flatPartialSum (D : BlockBasisData 𝕜 X) (N : ℕ) : X →L[𝕜] X :=
  ∑ n ∈ Finset.range N, (D.flatCoord n).smulRight (D.flatVector n)

theorem flatPartialSum_eq_projection (D : BlockBasisData 𝕜 X) (N : ℕ) :
    D.flatPartialSum N = D.flatProjection N := by
  induction N with
  | zero => simp [flatPartialSum]
  | succ N ih =>
    simp only [flatPartialSum, Finset.sum_range_succ]
    change D.flatPartialSum N + (D.flatCoord N).smulRight (D.flatVector N) = _
    rw [ih, D.flatProjection_succ]

theorem norm_flatPartialSum_le (D : BlockBasisData 𝕜 X) (N : ℕ) :
    ‖D.flatPartialSum N‖ ≤ 3 := by
  rw [D.flatPartialSum_eq_projection]
  exact D.projection_bound _ _ (blockEnumeration D.size_pos N).2.isLt.le

theorem flatPartialSum_apply (D : BlockBasisData 𝕜 X) (N : ℕ) (x : X) :
    D.flatPartialSum N x = ∑ n ∈ Finset.range N, D.flatCoord n x • D.flatVector n := by
  simp only [flatPartialSum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

theorem flatCoord_flatPartialSum (D : BlockBasisData 𝕜 X) (n N : ℕ) (x : X) :
    D.flatCoord n (D.flatPartialSum N x) = if n < N then D.flatCoord n x else 0 := by
  classical
  rw [D.flatPartialSum_apply]
  simp only [map_sum, map_smul, D.flat_biorthogonal, smul_eq_mul]
  simp

theorem flatPartialSum_comp_of_le (D : BlockBasisData 𝕜 X) {M N : ℕ} (hMN : M ≤ N)
    (x : X) : D.flatPartialSum N (D.flatPartialSum M x) = D.flatPartialSum M x := by
  classical
  rw [D.flatPartialSum_apply]
  simp only [D.flatCoord_flatPartialSum]
  rw [D.flatPartialSum_apply]
  calc
    (∑ i ∈ Finset.range N, (if i < M then D.flatCoord i x else 0) • D.flatVector i) =
        ∑ i ∈ Finset.range M, (if i < M then D.flatCoord i x else 0) • D.flatVector i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hMN)
      intro i _ hi
      have h : ¬ i < M := by simpa only [Finset.mem_range] using hi
      simp only [h, if_false, zero_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (Finset.mem_range.mp hi)]

theorem flatPartialSum_blockOffset (D : BlockBasisData 𝕜 X) (b : ℕ) :
    D.flatPartialSum (blockOffset D.size b) = D.projection b 0 := by
  rw [D.flatPartialSum_eq_projection]
  have he := blockEnumeration_encode D.size_pos (⟨b, ⟨0, D.size_pos b⟩⟩ : BlockPosition D.size)
  change blockEnumeration D.size_pos (blockOffset D.size b + 0) = _ at he
  simp only [Nat.add_zero] at he
  unfold flatProjection
  rw [he]

theorem flatPartialSum_tendsto (D : BlockBasisData 𝕜 X) (x : X) :
    Tendsto (fun N => D.flatPartialSum N x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨b, hb⟩ := (Metric.tendsto_atTop.1 (D.full_tendsto x)) (ε / 4) (by linarith)
  refine ⟨blockOffset D.size b, ?_⟩
  intro N hN
  have hclose := hb b (le_refl b)
  rw [dist_eq_norm, ← D.flatPartialSum_blockOffset b] at hclose
  have he : D.flatPartialSum N x - x =
      D.flatPartialSum N (x - D.flatPartialSum (blockOffset D.size b) x) +
        (D.flatPartialSum (blockOffset D.size b) x - x) := by
    rw [map_sub, D.flatPartialSum_comp_of_le hN]
    abel
  have hbound : ‖D.flatPartialSum N (x - D.flatPartialSum (blockOffset D.size b) x)‖ ≤
      3 * ‖D.flatPartialSum (blockOffset D.size b) x - x‖ := by
    calc
      _ ≤ ‖D.flatPartialSum N‖ * ‖x - D.flatPartialSum (blockOffset D.size b) x‖ :=
        (D.flatPartialSum N).le_opNorm _
      _ ≤ 3 * ‖D.flatPartialSum (blockOffset D.size b) x - x‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right (D.norm_flatPartialSum_le N) (norm_nonneg _)
  rw [dist_eq_norm, he]
  have hadd := norm_add_le
    (D.flatPartialSum N (x - D.flatPartialSum (blockOffset D.size b) x))
    (D.flatPartialSum (blockOffset D.size b) x - x)
  linarith

/-- The sequential Schauder basis obtained by visiting the blocks in order. -/
def schauderBasis (D : BlockBasisData 𝕜 X) : SchauderBasis 𝕜 X where
  vector := D.flatVector
  coord := D.flatCoord
  biorthogonal := D.flat_biorthogonal
  expansion := fun x => by
    simpa only [← D.flatPartialSum_apply] using D.flatPartialSum_tendsto x

theorem schauderBasis_partialSum (D : BlockBasisData 𝕜 X) (N : ℕ) :
    D.schauderBasis.partialSum N = D.flatProjection N := D.flatPartialSum_eq_projection N

theorem norm_schauderBasis_partialSum_le (D : BlockBasisData 𝕜 X) (N : ℕ) :
    ‖D.schauderBasis.partialSum N‖ ≤ 3 := D.norm_flatPartialSum_le N

end BlockBasisData

end LindenstraussRetraction
