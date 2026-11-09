import PL1.IntrinsicGraph
import PL1.L1Sum
import PL1.WeakSchur
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Coordinate approximation in countable `ℓ₁` sums

Uniform tails and coordinate norm convergence first give an elementary norm
convergence criterion. A full gliding-hump proof then shows that weak nullity
plus coordinate norm convergence already implies convergence in the actual
`ℓ₁` norm. This proves the Schur property for countable sums of a Schur space,
including genuine scalar `ℓ₁`, and gives the intrinsic graph's Schur property
when its coordinate operators are Dunford–Pettis.
-/

noncomputable section
open Filter
open scoped Topology

namespace PL1.L1Sum

variable {Y : Type*} [NormedAddCommGroup Y]

/-- Norm mass on the first `N` coordinates. -/
def headNorm (N : ℕ) (x : L1Sum Y) : ℝ :=
  ∑ n ∈ Finset.range N, ‖x n‖

/-- Norm mass on all coordinates from `N` onward. -/
def tailNorm (N : ℕ) (x : L1Sum Y) : ℝ :=
  ∑' n : ℕ, ‖x (n + N)‖

theorem headNorm_nonneg (N : ℕ) (x : L1Sum Y) : 0 ≤ headNorm N x :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem tailNorm_nonneg (N : ℕ) (x : L1Sum Y) : 0 ≤ tailNorm N x :=
  tsum_nonneg (fun _ => norm_nonneg _)

theorem norm_eq_headNorm_add_tailNorm (N : ℕ) (x : L1Sum Y) :
    ‖x‖ = headNorm N x + tailNorm N x := by
  rw [norm_eq_tsum]
  exact ((summable_norm x).sum_add_tsum_nat_add N).symm

/-- Every individual `ℓ₁` vector has vanishing tails. -/
theorem tailNorm_tendsto_zero (x : L1Sum Y) :
    Tendsto (fun N : ℕ => tailNorm N x) atTop (𝓝 0) := by
  have h := (summable_norm x).hasSum.tendsto_sum_nat
  rw [← norm_eq_tsum] at h
  have h' := (tendsto_const_nhds (x := ‖x‖)).sub h
  simp only [sub_self] at h'
  convert h' using 1
  funext N
  have hN := norm_eq_headNorm_add_tailNorm N x
  dsimp [headNorm] at hN
  linarith

/-- Uniform smallness of the norm mass outside one finite initial segment. -/
def HasUniformNormTails (x : ℕ → L1Sum Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, tailNorm N (x k) < ε

/-- Each fixed finite head converges in norm under coordinatewise convergence. -/
theorem headNorm_tendsto_zero {x : ℕ → L1Sum Y}
    (hx : ∀ n : ℕ, Tendsto (fun k => x k n) atTop (𝓝 0)) (N : ℕ) :
    Tendsto (fun k => headNorm N (x k)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range N)
    (fun n _ => tendsto_zero_iff_norm_tendsto_zero.mp (hx n))
  simpa only [headNorm, Finset.sum_const_zero] using h

/-- Coordinate norm convergence and uniform norm tails force `ℓ₁` convergence. -/
theorem tendsto_zero_of_coordinates_and_uniformTails {x : ℕ → L1Sum Y}
    (hx : ∀ n : ℕ, Tendsto (fun k => x k n) atTop (𝓝 0))
    (htail : HasUniformNormTails x) : Tendsto x atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := htail (ε / 2) (half_pos hε)
  have hhead := (headNorm_tendsto_zero hx N).eventually_lt_const (half_pos hε)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hhead
  refine ⟨K, fun k hk => ?_⟩
  rw [dist_zero_right, norm_eq_headNorm_add_tailNorm N]
  have h₁ := hN k
  have h₂ := hK k hk
  linarith

/-- Restriction of an `ℓ₁` vector to a finite interval of coordinates. -/
def block (N M : ℕ) (x : L1Sum Y) : L1Sum Y :=
  ∑ i ∈ Finset.Ico N M, lp.single 1 i (x i)

theorem block_apply (N M : ℕ) (x : L1Sum Y) (i : ℕ) :
    block N M x i = if i ∈ Finset.Ico N M then x i else 0 := by
  simp only [block, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single,
    Finset.sum_pi_single]

theorem norm_sub_block {N M : ℕ} (hNM : N ≤ M) (x : L1Sum Y) :
    ‖x - block N M x‖ = headNorm N x + tailNorm M x := by
  have h := lp.norm_compl_sum_single (by norm_num : 0 < (1 : ENNReal).toReal)
    x (Finset.Ico N M)
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  rw [Finset.sum_Ico_eq_sub (fun i : ℕ => ‖x i‖) hNM] at h
  have hM := norm_eq_headNorm_add_tailNorm M x
  dsimp [block, headNorm] at hM ⊢
  linarith

/-- The finite-block extraction underlying the gliding-hump argument. A
coordinatewise null sequence which is not norm null has a subsequence uniformly
close to disjoint blocks, while keeping its norm bounded away from zero. -/
theorem exists_disjoint_blocks_of_not_tendsto {x : ℕ → L1Sum Y}
    (hx : ∀ i : ℕ, Tendsto (fun k => x k i) atTop (𝓝 0))
    (hn : ¬ Tendsto x atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n : ℕ → ℕ, (∀ k, k ≤ n k) ∧
      ∃ s : ℕ → Finset ℕ, Pairwise (fun k l => Disjoint (s k) (s l)) ∧
        ∃ v : ℕ → L1Sum Y,
          (∀ k i : ℕ, i ∉ s k → v k i = 0) ∧
          ∀ k : ℕ, ε ≤ ‖x (n k)‖ ∧ ‖x (n k) - v k‖ < ε / 4 := by
  classical
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε, hε, hbad⟩ := hn
  simp only [dist_zero_right] at hbad
  have hstep : ∀ N k : ℕ, ∃ n M : ℕ,
      k ≤ n ∧ N < M ∧ ε ≤ ‖x n‖ ∧
      headNorm N (x n) < ε / 8 ∧ tailNorm M (x n) < ε / 8 := by
    intro N k
    have hε8 : 0 < ε / 8 := by positivity
    obtain ⟨K, hK⟩ := eventually_atTop.mp
      ((headNorm_tendsto_zero hx N).eventually_lt_const hε8)
    obtain ⟨n, hn, hnorm⟩ := hbad (max k K)
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((tailNorm_tendsto_zero (x n)).eventually_lt_const hε8)
    refine ⟨n, max (N + 1) M, (le_max_left k K).trans hn, ?_, hnorm, ?_, ?_⟩
    · exact (Nat.lt_succ_self N).trans_le (le_max_left _ _)
    · exact hK n ((le_max_right k K).trans hn)
    · exact hM _ (le_max_right _ _)
  choose a b ha hb hnorm hhead htail using hstep
  let cut : ℕ → ℕ := Nat.rec 0 (fun k N => b N k)
  have hcutstep : ∀ k : ℕ, cut k < cut (k + 1) := by
    intro k
    change cut k < b (cut k) k
    exact hb _ _
  have hcut : StrictMono cut := strictMono_nat_of_lt_succ hcutstep
  let n : ℕ → ℕ := fun k => a (cut k) k
  let s : ℕ → Finset ℕ := fun k => Finset.Ico (cut k) (cut (k + 1))
  let v : ℕ → L1Sum Y := fun k => block (cut k) (cut (k + 1)) (x (n k))
  refine ⟨ε, hε, n, (fun k => ha _ _), s, ?_, v, ?_, ?_⟩
  · intro k l hkl
    apply Finset.disjoint_left.mpr
    intro i hik hil
    have hik' := Finset.mem_Ico.mp hik
    have hil' := Finset.mem_Ico.mp hil
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · have hbound := hcut.monotone (Nat.succ_le_of_lt hlt)
      change cut (k + 1) ≤ cut l at hbound
      omega
    · have hbound := hcut.monotone (Nat.succ_le_of_lt hgt)
      change cut (l + 1) ≤ cut k at hbound
      omega
  · intro k i hi
    exact (block_apply (cut k) (cut (k + 1)) (x (n k)) i).trans (ite_eq_right hi)
  · intro k
    refine ⟨hnorm _ _, ?_⟩
    change ‖x (n k) - block (cut k) (cut (k + 1)) (x (n k))‖ < ε / 4
    rw [norm_sub_block (hcutstep k).le]
    have hh : headNorm (cut k) (x (n k)) < ε / 8 := hhead _ _
    have ht : tailNorm (cut (k + 1)) (x (n k)) < ε / 8 := htail _ _
    linarith

section DualBlocks

variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 Y]

/-- A single bounded functional norms every member of a sequence supported on
pairwise disjoint finite coordinate sets. This is the duality step in the
gliding-hump argument for countable `ℓ₁` sums. -/
theorem exists_dual_norming_disjoint_blocks (v : ℕ → L1Sum Y)
    (s : ℕ → Finset ℕ) (hs : Pairwise (fun k l => Disjoint (s k) (s l)))
    (hv : ∀ k i : ℕ, i ∉ s k → v k i = 0) :
    ∃ φ : L1Sum Y →L[𝕜] 𝕜, ‖φ‖ ≤ 1 ∧ ∀ k : ℕ, φ (v k) = (‖v k‖ : 𝕜) := by
  classical
  choose ψ hψnorm hψvalue using fun k i : ℕ => exists_dual_vector'' 𝕜 (v k i)
  let α : ℕ → Y →L[𝕜] 𝕜 := fun i =>
    if h : ∃ k : ℕ, i ∈ s k then ψ h.choose i else 0
  have hαnorm : ∀ i : ℕ, ‖α i‖ ≤ 1 := by
    intro i
    dsimp [α]
    split_ifs with h
    · exact hψnorm _ _
    · simp
  have hαvalue : ∀ k i : ℕ, α i (v k i) = (‖v k i‖ : 𝕜) := by
    intro k i
    by_cases hi : i ∈ s k
    · have hex : ∃ l : ℕ, i ∈ s l := ⟨k, hi⟩
      have hk : hex.choose = k := by
        by_contra hne
        exact Finset.disjoint_left.mp (hs hne) hex.choose_spec hi
      dsimp [α]
      rw [dite_eq_left hex]
      simpa only [hk] using hψvalue hex.choose i
    · rw [hv k i hi, map_zero, norm_zero, RCLike.ofReal_zero]
  refine ⟨synthesis α 1 hαnorm, norm_synthesis_le α 1 hαnorm zero_le_one, ?_⟩
  intro k
  rw [synthesis_apply]
  simp_rw [hαvalue]
  change (∑' i : ℕ, (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ‖v k i‖) =
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ‖v k‖
  rw [← (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).map_tsum (summable_norm (v k))]
  rw [← norm_eq_tsum]

/-- The relative Schur theorem for an actual countable `ℓ₁` sum: a weakly null
sequence is norm null as soon as every coordinate is norm null. No uniform-tail
hypothesis is required; it is replaced by a proved gliding-hump contradiction. -/
theorem tendsto_zero_of_weaklyConverges_and_coordinates {x : ℕ → L1Sum Y}
    (hweak : WeaklyConverges 𝕜 (L1Sum Y) x 0)
    (hcoord : ∀ i : ℕ, Tendsto (fun k => x k i) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  by_contra hn
  obtain ⟨ε, hε, n, hn, s, hs, v, hv, hnorm⟩ :=
    exists_disjoint_blocks_of_not_tendsto hcoord hn
  obtain ⟨φ, hφ, hvalue⟩ := exists_dual_norming_disjoint_blocks 𝕜 v s hs hv
  have hn_top : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hlim : Tendsto (fun k => φ (x (n k))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using (hweak φ).comp hn_top
  have hlimnorm := tendsto_zero_iff_norm_tendsto_zero.mp hlim
  obtain ⟨k, hk⟩ := (hlimnorm.eventually_lt_const (half_pos hε)).exists
  have herror : ‖φ (x (n k) - v k)‖ ≤ ‖x (n k) - v k‖ := by
    calc
      ‖φ (x (n k) - v k)‖ ≤ ‖φ‖ * ‖x (n k) - v k‖ := φ.le_opNorm _
      _ ≤ 1 * ‖x (n k) - v k‖ :=
        mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
      _ = ‖x (n k) - v k‖ := one_mul _
  have hvalueNorm : ‖φ (v k)‖ = ‖v k‖ := by
    rw [hvalue]
    simp
  have hφtriangle : ‖v k‖ ≤ ‖φ (x (n k))‖ + ‖φ (x (n k) - v k)‖ := by
    calc
      ‖v k‖ = ‖φ (v k)‖ := hvalueNorm.symm
      _ = ‖φ (x (n k)) - φ (x (n k) - v k)‖ := by
        rw [map_sub, sub_sub_cancel]
      _ ≤ ‖φ (x (n k))‖ + ‖φ (x (n k) - v k)‖ := norm_sub_le _ _
  have hxtriangle : ‖x (n k)‖ ≤ ‖x (n k) - v k‖ + ‖v k‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x (n k) - v k) (v k)
  obtain ⟨hlarge, hclose⟩ := hnorm k
  linarith

/-- Countable `ℓ₁` sums of a Schur space are Schur. -/
theorem hasSchurProperty (hY : HasSchurProperty 𝕜 Y) :
    HasSchurProperty 𝕜 (L1Sum Y) := by
  intro x a hx
  have hweak := weaklyConverges_iff_sub_const.mp hx
  have hzero : Tendsto (fun k => x k - a) atTop (𝓝 0) := by
    apply tendsto_zero_of_weaklyConverges_and_coordinates 𝕜 hweak
    intro i
    have hc := hY _ _ (hweak.map (lp.evalCLM 𝕜 (fun _ : ℕ => Y) 1 i))
    change Tendsto (fun k => (x k - a) i) atTop (𝓝 ((0 : L1Sum Y) i)) at hc
    simpa using hc
  simpa only [sub_add_cancel, zero_add] using
    hzero.add (tendsto_const_nhds (x := a))

end DualBlocks

/-- Schur's theorem for the genuine scalar absolutely summable sequence space,
over either the real or complex field. -/
theorem _root_.PL1.ell1_hasSchurProperty (𝕜 : Type*) [RCLike 𝕜] :
    HasSchurProperty 𝕜 (Ell1 𝕜) := by
  apply L1Sum.hasSchurProperty 𝕜
  intro x a hx
  simpa only [ContinuousLinearMap.id_apply] using hx (ContinuousLinearMap.id 𝕜 𝕜)

end PL1.L1Sum

namespace PL1.IntrinsicGraph

variable {𝕜 Y : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (D : ℕ → Y →L[𝕜] Y)

/-- Coordinate Dunford–Pettis operators alone suffice for the Schur property
of the intrinsic graph. The countable `ℓ₁` argument is fully proved above. -/
theorem hasSchurProperty_of_coordinateDP
    (hcoord : ∀ n : ℕ, IsDunfordPettis (coord D n)) :
    HasSchurProperty 𝕜 (Space D) := by
  intro x a hx
  have hweak := weaklyConverges_iff_sub_const.mp hx
  have hzero : Tendsto (fun k => x k - a) atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    apply L1Sum.tendsto_zero_of_weaklyConverges_and_coordinates 𝕜
    · change WeaklyConverges 𝕜 (L1Sum Y) (fun k => inclusion D (x k - a)) 0
      have hi := hweak.map (inclusion D).toContinuousLinearMap
      change WeaklyConverges 𝕜 (L1Sum Y) (fun k => inclusion D (x k - a))
        (inclusion D 0) at hi
      simpa only [map_zero] using hi
    · intro n
      simpa only [coord_apply, map_zero] using hcoord n (fun k => x k - a) 0 hweak
  simpa only [sub_add_cancel, zero_add] using
    hzero.add (tendsto_const_nhds (x := a))

/-- Since every graph coordinate factors through coordinate zero, it suffices
to check the Dunford–Pettis property of the underlying-vector recovery map. -/
theorem hasSchurProperty_iff_evalZero_isDunfordPettis :
    HasSchurProperty 𝕜 (Space D) ↔ IsDunfordPettis (evalZero D) := by
  constructor
  · intro h x a hx
    exact ((evalZero D).continuous.tendsto a).comp (h x a hx)
  · intro h
    apply hasSchurProperty_of_coordinateDP D
    intro n
    have hfactor : coord D n = (D n).comp (evalZero D) := by
      ext x
      exact coord_eq D n x
    rw [hfactor]
    exact h.comp_left (D n)

/-- A precise approximation criterion for the intrinsic graph's Schur property.
The uniform-tail conclusion for weakly null graph sequences is a separate,
explicit hypothesis, to be established in applications. -/
theorem hasSchurProperty_of_coordinateDP_and_uniformTails
    (hcoord : ∀ n : ℕ, IsDunfordPettis (coord D n))
    (htail : ∀ x : ℕ → Space D, WeaklyConverges 𝕜 (Space D) x 0 →
      L1Sum.HasUniformNormTails (fun k => inclusion D (x k))) :
    HasSchurProperty 𝕜 (Space D) := by
  intro x a hx
  have hweak := weaklyConverges_iff_sub_const.mp hx
  have hzero : Tendsto (fun k => x k - a) atTop (𝓝 0) := by
    apply tendsto_subtype_rng.mpr
    apply L1Sum.tendsto_zero_of_coordinates_and_uniformTails
    · intro n
      simpa only [coord_apply, map_zero] using hcoord n (fun k => x k - a) 0 hweak
    · exact htail (fun k => x k - a) hweak
  simpa only [sub_add_cancel, zero_add] using
    hzero.add (tendsto_const_nhds (x := a))

end PL1.IntrinsicGraph
