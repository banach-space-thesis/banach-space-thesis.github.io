import LindenstraussRetraction.C0SumCoordinates
import LindenstraussRetraction.BlockBasis
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-! Interleaving the finite basis blocks of the coordinates of a dependent c₀ sum. -/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace LindenstraussRetraction

/-- The first local block in coordinate `n` which has not been visited before
global block `b`. The pairing function orders each coordinate's blocks. -/
def directSumLocalStage (n b : ℕ) : ℕ :=
  Nat.find (show ∃ k, b ≤ Nat.pair n k from ⟨b, Nat.right_le_pair n b⟩)

theorem directSumLocalStage_spec (n b : ℕ) : b ≤ Nat.pair n (directSumLocalStage n b) := by
  exact Nat.find_spec (show ∃ k, b ≤ Nat.pair n k from ⟨b, Nat.right_le_pair n b⟩)

theorem directSumLocalStage_min {n b k : ℕ} (hk : k < directSumLocalStage n b) :
    Nat.pair n k < b := by
  exact Nat.lt_of_not_ge (Nat.find_min
    (show ∃ j, b ≤ Nat.pair n j from ⟨b, Nat.right_le_pair n b⟩) hk)

theorem directSumLocalStage_pair (n k : ℕ) : directSumLocalStage n (Nat.pair n k) = k := by
  apply (Nat.find_eq_iff _).2
  refine ⟨le_refl _, fun j hj => ?_⟩
  exact not_le_of_gt (Nat.pair_lt_pair_right n hj)

theorem directSumLocalStage_zero (n : ℕ) : directSumLocalStage n 0 = 0 := by
  apply (Nat.find_eq_zero _).2
  exact Nat.zero_le _

theorem directSumLocalStage_eq_zero_of_le {n b : ℕ} (h : b ≤ n) :
    directSumLocalStage n b = 0 := by
  apply (Nat.find_eq_zero _).2
  exact h.trans (Nat.left_le_pair n 0)

theorem directSumLocalStage_current (b : ℕ) :
    directSumLocalStage (Nat.unpair b).1 b = (Nat.unpair b).2 := by
  conv_lhs => arg 2; rw [← Nat.pair_unpair b]
  exact directSumLocalStage_pair _ _

theorem directSumLocalStage_pair_succ (n k : ℕ) :
    directSumLocalStage n (Nat.pair n k + 1) = k + 1 := by
  apply (Nat.find_eq_iff _).2
  refine ⟨Nat.succ_le_of_lt (Nat.pair_lt_pair_right n (Nat.lt_succ_self k)), fun j hj => ?_⟩
  have hmono : Monotone (fun k => Nat.pair n k) :=
    (show StrictMono (fun k => Nat.pair n k) from fun _ _ h => Nat.pair_lt_pair_right n h).monotone
  exact not_le_of_gt (Nat.lt_succ_of_le (hmono (Nat.le_of_lt_succ hj)))

theorem directSumLocalStage_current_succ (b : ℕ) :
    directSumLocalStage (Nat.unpair b).1 (b + 1) = (Nat.unpair b).2 + 1 := by
  conv_lhs => arg 2; arg 1; rw [← Nat.pair_unpair b]
  exact directSumLocalStage_pair_succ _ _

theorem directSumLocalStage_succ_of_ne (n b : ℕ) (hn : n ≠ (Nat.unpair b).1) :
    directSumLocalStage n (b + 1) = directSumLocalStage n b := by
  apply le_antisymm
  · apply Nat.find_min'
    have h := directSumLocalStage_spec n b
    have hne : Nat.pair n (directSumLocalStage n b) ≠ b := by
      intro he
      have hh := congrArg (fun t => (Nat.unpair t).1) he
      simp only [Nat.unpair_pair] at hh
      exact hn hh
    omega
  · apply Nat.find_min'
    exact (Nat.le_succ b).trans (directSumLocalStage_spec n (b + 1))

theorem directSumLocalStage_tendsto (n : ℕ) :
    Tendsto (directSumLocalStage n) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (Nat.pair n K)] with b hb
  by_contra h
  have hlt := Nat.pair_lt_pair_right n (Nat.lt_of_not_ge h)
  have hs := directSumLocalStage_spec n b
  omega

universe u v
variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : ℕ → Type u) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
variable (D : ∀ n, BlockBasisData 𝕜 (E n))

def directSumPacketSize (b : ℕ) : ℕ := (D (Nat.unpair b).1).size (Nat.unpair b).2

def directSumPacketPosition (p : BlockPosition (directSumPacketSize 𝕜 E D)) :
    (n : ℕ) × BlockPosition (D n).size :=
  ⟨(Nat.unpair p.1).1, ⟨(Nat.unpair p.1).2, p.2⟩⟩

theorem directSumPacketPosition_injective :
    Function.Injective (directSumPacketPosition 𝕜 E D) := by
  intro p q h
  have hn := congrArg (fun t => t.1) h
  change (Nat.unpair p.1).1 = (Nat.unpair q.1).1 at hn
  have hk : (Nat.unpair p.1).2 = (Nat.unpair q.1).2 := by
    exact congrArg (fun t => t.2.1) h
  have hb : p.1 = q.1 := by
    rw [← Nat.pair_unpair p.1, ← Nat.pair_unpair q.1, hn, hk]
  cases p with | mk b i =>
    cases q with | mk c j =>
      dsimp only at hb
      subst c
      have hi : i = j := by
        exact Fin.ext (congrArg (fun t => t.2.2.val) h)
      subst j
      rfl

def directSumLocalVector (p : (n : ℕ) × BlockPosition (D n).size) : C0Sum 𝕜 E :=
  c0SumSingle 𝕜 E p.1 ((D p.1).vector p.2.1 p.2.2)

def directSumLocalCoord (p : (n : ℕ) × BlockPosition (D n).size) : C0Sum 𝕜 E →L[𝕜] 𝕜 :=
  ((D p.1).coord p.2.1 p.2.2).comp (c0SumCoordinate 𝕜 E p.1)

theorem directSumLocal_biorthogonal
    (p q : (n : ℕ) × BlockPosition (D n).size) :
    directSumLocalCoord 𝕜 E D p (directSumLocalVector 𝕜 E D q) =
      if p = q then 1 else 0 := by
  classical
  rcases p with ⟨n, ⟨k, i⟩⟩
  rcases q with ⟨m, ⟨l, j⟩⟩
  by_cases hnm : n = m
  · subst m
    simp only [directSumLocalCoord, directSumLocalVector, ContinuousLinearMap.comp_apply,
      c0SumCoordinate_single]
    rw [(D n).biorthogonal ⟨k, i⟩ ⟨l, j⟩]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · have hpq : (⟨n, ⟨k, i⟩⟩ : (n : ℕ) × BlockPosition (D n).size) ≠ ⟨m, ⟨l, j⟩⟩ :=
      fun h => hnm (congrArg Sigma.fst h)
    rw [if_neg hpq]
    simp only [directSumLocalCoord, directSumLocalVector, ContinuousLinearMap.comp_apply,
      c0SumCoordinate_apply, c0SumSingle_apply_ne 𝕜 E m n _ hnm, map_zero]

def directSumPacketVector (b : ℕ) (i : Fin (directSumPacketSize 𝕜 E D b)) : C0Sum 𝕜 E :=
  directSumLocalVector 𝕜 E D (directSumPacketPosition 𝕜 E D ⟨b, i⟩)

def directSumPacketCoord (b : ℕ) (i : Fin (directSumPacketSize 𝕜 E D b)) : C0Sum 𝕜 E →L[𝕜] 𝕜 :=
  directSumLocalCoord 𝕜 E D (directSumPacketPosition 𝕜 E D ⟨b, i⟩)

theorem directSumPacket_biorthogonal (p q : BlockPosition (directSumPacketSize 𝕜 E D)) :
    directSumPacketCoord 𝕜 E D p.1 p.2 (directSumPacketVector 𝕜 E D q.1 q.2) =
      if p = q then 1 else 0 := by
  classical
  rw [directSumPacketCoord, directSumPacketVector, directSumLocal_biorthogonal]
  congr 1
  exact propext (directSumPacketPosition_injective 𝕜 E D).eq_iff

/-- Coordinate `n`'s projection while global block `b` is partly traversed. -/
def directSumCoordinateProjection (n b r : ℕ) : E n →L[𝕜] E n :=
  if n = (Nat.unpair b).1 then (D n).projection (Nat.unpair b).2 r
  else (D n).projection (directSumLocalStage n b) 0

theorem directSumCoordinateProjection_zero_stage (n b : ℕ) :
    directSumCoordinateProjection 𝕜 E D n b 0 = (D n).projection (directSumLocalStage n b) 0 := by
  unfold directSumCoordinateProjection
  split_ifs with h
  · subst n
    rw [directSumLocalStage_current]
  · rfl

theorem directSumCoordinateProjection_eq_zero {n b r : ℕ} (hn : b < n) :
    directSumCoordinateProjection 𝕜 E D n b r = 0 := by
  have hne : n ≠ (Nat.unpair b).1 := by
    intro h
    have hle := Nat.unpair_left_le b
    omega
  rw [directSumCoordinateProjection, if_neg hne,
    directSumLocalStage_eq_zero_of_le hn.le, (D n).projection_zero]

def directSumPacketProjection (b r : ℕ) : C0Sum 𝕜 E →L[𝕜] C0Sum 𝕜 E :=
  ∑ n ∈ Finset.range (b + 1), (c0SumSingle 𝕜 E n).comp
    ((directSumCoordinateProjection 𝕜 E D n b r).comp (c0SumCoordinate 𝕜 E n))

theorem directSumPacketProjection_apply (b r : ℕ) (x : C0Sum 𝕜 E) (m : ℕ) :
    (directSumPacketProjection 𝕜 E D b r x).val m =
      directSumCoordinateProjection 𝕜 E D m b r (x.val m) := by
  classical
  change c0SumCoordinate 𝕜 E m (directSumPacketProjection 𝕜 E D b r x) = _
  simp only [directSumPacketProjection, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.comp_apply, c0SumCoordinate_apply]
  by_cases hm : m < b + 1
  · rw [Finset.sum_eq_single m]
    · exact lp.single_apply_self ∞ m _
    · intro n _ hnm
      exact lp.single_apply_ne ∞ n _ (Ne.symm hnm)
    · intro h
      exact (h (Finset.mem_range.mpr hm)).elim
  · rw [directSumCoordinateProjection_eq_zero 𝕜 E D (by omega : b < m),
      ContinuousLinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro n hn
    apply lp.single_apply_ne
    intro h
    exact hm (h ▸ Finset.mem_range.mp hn)

theorem directSumCoordinateProjection_boundary (n b : ℕ) :
    directSumCoordinateProjection 𝕜 E D n b (directSumPacketSize 𝕜 E D b) =
      directSumCoordinateProjection 𝕜 E D n (b + 1) 0 := by
  rw [directSumCoordinateProjection_zero_stage]
  unfold directSumCoordinateProjection
  split_ifs with h
  · subst n
    change (D (Nat.unpair b).1).projection (Nat.unpair b).2
      ((D (Nat.unpair b).1).size (Nat.unpair b).2) = _
    rw [(D (Nat.unpair b).1).projection_boundary, directSumLocalStage_current_succ]
  · rw [directSumLocalStage_succ_of_ne n b h]

theorem directSumPacketProjection_boundary (b : ℕ) :
    directSumPacketProjection 𝕜 E D b (directSumPacketSize 𝕜 E D b) =
      directSumPacketProjection 𝕜 E D (b + 1) 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply lp.ext
  funext n
  rw [directSumPacketProjection_apply, directSumPacketProjection_apply,
    directSumCoordinateProjection_boundary]

theorem directSumPacketProjection_zero : directSumPacketProjection 𝕜 E D 0 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply lp.ext
  funext n
  rw [directSumPacketProjection_apply, directSumCoordinateProjection_zero_stage,
    directSumLocalStage_zero, (D n).projection_zero]
  rfl

theorem directSumPacketProjection_norm_le (b r : ℕ) (hr : r ≤ directSumPacketSize 𝕜 E D b) :
    ‖directSumPacketProjection 𝕜 E D b r‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  apply c0Sum_norm_le 𝕜 E (by positivity : 0 ≤ 3 * ‖x‖)
  intro n
  rw [directSumPacketProjection_apply]
  have hproj : ‖directSumCoordinateProjection 𝕜 E D n b r‖ ≤ 3 := by
    unfold directSumCoordinateProjection
    split_ifs with h
    · subst n
      exact (D _).projection_bound _ _ hr
    · exact (D n).projection_bound _ _ (Nat.zero_le _)
  exact ((directSumCoordinateProjection 𝕜 E D n b r).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right hproj (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (c0Sum_norm_coordinate_le 𝕜 E x n) (by norm_num)))

theorem directSumPacketProjection_step (b : ℕ) (i : Fin (directSumPacketSize 𝕜 E D b)) :
    directSumPacketProjection 𝕜 E D b (i.val + 1) = directSumPacketProjection 𝕜 E D b i.val +
      (directSumPacketCoord 𝕜 E D b i).smulRight (directSumPacketVector 𝕜 E D b i) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply lp.ext
  funext m
  change (directSumPacketProjection 𝕜 E D b (i.val + 1) x).val m =
    (directSumPacketProjection 𝕜 E D b i.val x).val m +
      (directSumPacketCoord 𝕜 E D b i x) • (directSumPacketVector 𝕜 E D b i).val m
  rw [directSumPacketProjection_apply, directSumPacketProjection_apply]
  by_cases hm : m = (Nat.unpair b).1
  · subst m
    simp only [directSumCoordinateProjection, directSumPacketCoord,
      directSumPacketVector, directSumLocalCoord, directSumLocalVector, directSumPacketPosition,
      ContinuousLinearMap.comp_apply, c0SumCoordinate_apply, c0SumSingle_apply_self]
    exact congrArg (fun f : E (Nat.unpair b).1 →L[𝕜] E (Nat.unpair b).1 =>
      f (x.val (Nat.unpair b).1)) ((D _).projection_step (Nat.unpair b).2 i)
  · simp only [directSumCoordinateProjection, if_neg hm, directSumPacketVector,
      directSumLocalVector, directSumPacketPosition, c0SumSingle_apply_ne 𝕜 E _ m _ hm,
      smul_zero, add_zero]

theorem directSumPacketProjection_tendsto (x : C0Sum 𝕜 E) :
    Tendsto (fun b => directSumPacketProjection 𝕜 E D b 0 x) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 x.property) (ε / 8) (by positivity)
  have hhead : ∀ᶠ b in atTop, ∀ n : Fin K,
      ‖(D n.val).projection (directSumLocalStage n.val b) 0 (x.val n.val) - x.val n.val‖ < ε / 2 := by
    apply Filter.eventually_all.2
    intro n
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.1 (((D n.val).full_tendsto (x.val n.val)).comp
        (directSumLocalStage_tendsto n.val))) (ε / 2) (half_pos hε)
  filter_upwards [hhead] with b hhead
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) ?_ (half_lt_self hε)
  apply c0Sum_norm_le 𝕜 E (half_pos hε).le
  intro m
  change ‖(directSumPacketProjection 𝕜 E D b 0 x).val m - x.val m‖ ≤ ε / 2
  rw [directSumPacketProjection_apply, directSumCoordinateProjection_zero_stage]
  by_cases hmK : m < K
  · exact (hhead ⟨m, hmK⟩).le
  · have htail : ‖x.val m‖ < ε / 8 := by
      simpa only [dist_zero_right, norm_norm] using hK m (Nat.le_of_not_lt hmK)
    have hproj : ‖(D m).projection (directSumLocalStage m b) 0 (x.val m)‖ ≤ 3 * ‖x.val m‖ :=
      (((D m).projection _ 0).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((D m).projection_bound _ 0 (Nat.zero_le _)) (norm_nonneg _))
    exact (norm_sub_le _ _).trans (by linarith)

/-- A uniformly bounded finite-block basis packet on the entire c₀ sum. -/
def directSumBlockBasisData : BlockBasisData 𝕜 (C0Sum 𝕜 E) where
  size := directSumPacketSize 𝕜 E D
  size_pos := fun b => (D (Nat.unpair b).1).size_pos (Nat.unpair b).2
  vector := directSumPacketVector 𝕜 E D
  coord := directSumPacketCoord 𝕜 E D
  biorthogonal := directSumPacket_biorthogonal 𝕜 E D
  projection := directSumPacketProjection 𝕜 E D
  projection_zero := directSumPacketProjection_zero 𝕜 E D
  projection_boundary := directSumPacketProjection_boundary 𝕜 E D
  projection_step := directSumPacketProjection_step 𝕜 E D
  projection_bound := directSumPacketProjection_norm_le 𝕜 E D
  full_tendsto := directSumPacketProjection_tendsto 𝕜 E D

/-- Flattening the paired finite blocks gives a sequential Schauder basis. -/
def c0SumPacketSchauderBasis : SchauderBasis 𝕜 (C0Sum 𝕜 E) :=
  (directSumBlockBasisData 𝕜 E D).schauderBasis

theorem norm_c0SumPacketSchauderBasis_partialSum_le (N : ℕ) :
    ‖(c0SumPacketSchauderBasis 𝕜 E D).partialSum N‖ ≤ 3 :=
  (directSumBlockBasisData 𝕜 E D).norm_schauderBasis_partialSum_le N

end LindenstraussRetraction
