import PL1.WeakSchur
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-rank approximation and Dunford–Pettis operators

The boundedness of weakly convergent sequences is proved using Banach–Steinhaus
and the canonical isometric embedding into the double dual. It is not an extra
hypothesis in the approximation results.
-/

noncomputable section

open Filter
open scoped Topology

namespace PL1

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem isDunfordPettis_zero : IsDunfordPettis (0 : E →L[𝕜] F) := by
  intro x a hx
  exact tendsto_const_nhds

theorem IsDunfordPettis.add {S T : E →L[𝕜] F}
    (hS : IsDunfordPettis S) (hT : IsDunfordPettis T) : IsDunfordPettis (S + T) := by
  intro x a hx
  exact (hS x a hx).add (hT x a hx)

theorem IsDunfordPettis.smul {T : E →L[𝕜] F} (hT : IsDunfordPettis T) (c : 𝕜) :
    IsDunfordPettis (c • T) := by
  intro x a hx
  exact (hT x a hx).const_smul c

/-- The Dunford–Pettis operators are a linear subspace of bounded operators. -/
def dunfordPettisSubmodule : Submodule 𝕜 (E →L[𝕜] F) where
  carrier := {T | IsDunfordPettis T}
  zero_mem' := isDunfordPettis_zero
  add_mem' := fun hS hT => hS.add hT
  smul_mem' := fun c _T hT => hT.smul c

/-- Weakly convergent sequences are norm bounded; completeness of E is unnecessary. -/
theorem WeaklyConverges.exists_norm_bound {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun n => NormedSpace.inclusionInDoubleDual 𝕜 E (x n)) (by
      intro φ
      obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (hx φ)).exists_norm_le
      exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩)
  refine ⟨C, fun n => ?_⟩
  have hn := hC n
  change ‖NormedSpace.inclusionInDoubleDualLi 𝕜 (x n)‖ ≤ C at hn
  rw [(NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map] at hn
  exact hn

/-- A strictly positive uniform bound is convenient for quantitative approximation. -/
theorem WeaklyConverges.exists_pos_norm_bound {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) : ∃ C : ℝ, 0 < C ∧ ∀ n, ‖x n‖ ≤ C := by
  obtain ⟨C, hC⟩ := hx.exists_norm_bound
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun n => (hC n).trans (le_max_left _ _)⟩

theorem WeaklyConverges.isBounded_range {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) : Bornology.IsBounded (Set.range x) := by
  obtain ⟨C, hC⟩ := hx.exists_norm_bound
  exact isBounded_iff_forall_norm_le.mpr ⟨C, by simpa using hC⟩

/-- The full dual separates points, so a weak limit in a normed space is unique. -/
theorem WeaklyConverges.unique {x : ℕ → E} {a b : E}
    (ha : WeaklyConverges 𝕜 E x a) (hb : WeaklyConverges 𝕜 E x b) : a = b := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
  intro φ
  exact tendsto_nhds_unique (ha φ) (hb φ)

theorem WeaklyConverges.subseq {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) {r : ℕ → ℕ} (hr : StrictMono r) :
    WeaklyConverges 𝕜 E (x ∘ r) a := by
  intro φ
  exact (hx φ).comp hr.tendsto_atTop

/-- A weakly convergent sequence contained in a norm-compact set converges in norm. -/
theorem WeaklyConverges.tendsto_of_isCompact {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) {K : Set E} (hK : IsCompact K)
    (hxK : ∀ n, x n ∈ K) : Tendsto x atTop (𝓝 a) := by
  by_contra hconv
  rw [Metric.tendsto_atTop] at hconv
  push Not at hconv
  obtain ⟨ε, hε, hbad⟩ := hconv
  have hcompact : IsCompact (K ∩ {y : E | ε ≤ dist y a}) :=
    hK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfreq : ∃ᶠ n in atTop, x n ∈ K ∩ {y : E | ε ≤ dist y a} := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n, hn, hdist⟩ := hbad N
    exact ⟨n, hn, hxK n, hdist⟩
  obtain ⟨b, hb, r, hr, hsub⟩ := hcompact.tendsto_subseq' hfreq
  have hba : b = a := (weaklyConverges_of_tendsto hsub).unique (hx.subseq hr)
  have hbε : ε ≤ 0 := by
    simpa only [Set.mem_ofPred_eq, hba, dist_self] using hb.2
  exact (not_le_of_gt hε) hbε

/-- Relative norm compactness is enough in the previous result. -/
theorem WeaklyConverges.tendsto_of_isCompact_closure {x : ℕ → E} {a : E}
    (hx : WeaklyConverges 𝕜 E x a) (hc : IsCompact (closure (Set.range x))) :
    Tendsto x atTop (𝓝 a) :=
  hx.tendsto_of_isCompact hc (fun n => subset_closure ⟨n, rfl⟩)

/-- In a Banach space, a weakly convergent sequence with totally bounded range
converges in norm. This is the compactness step in the paper's restriction criterion. -/
theorem WeaklyConverges.tendsto_of_totallyBounded [CompleteSpace E]
    {x : ℕ → E} {a : E} (hx : WeaklyConverges 𝕜 E x a)
    (htb : TotallyBounded (Set.range x)) : Tendsto x atTop (𝓝 a) :=
  hx.tendsto_of_isCompact_closure (htb.closure.isCompact_of_isClosed isClosed_closure)

/-- Finite-dimensional normed spaces have the Schur property. -/
theorem hasSchurProperty_of_finiteDimensional [FiniteDimensional 𝕜 E] :
    HasSchurProperty 𝕜 E := by
  let e := (Module.finBasis 𝕜 E).equivFunL
  intro x a hx
  have hcoord : Tendsto (fun n => e (x n)) atTop (𝓝 (e a)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hx ((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap)
  simpa [Function.comp_def] using (e.symm.continuous.tendsto (e a)).comp hcoord

/-- Every bounded linear operator of finite rank is Dunford–Pettis. -/
theorem isDunfordPettis_of_finiteDimensional_range (T : E →L[𝕜] F)
    [FiniteDimensional 𝕜 T.range] : IsDunfordPettis T :=
  isDunfordPettis_of_hasSchurProperty_range T hasSchurProperty_of_finiteDimensional

/-- Limits in operator norm of Dunford–Pettis operators are Dunford–Pettis. -/
theorem isDunfordPettis_of_tendsto {T : ℕ → E →L[𝕜] F} {S : E →L[𝕜] F}
    (hT : ∀ m, IsDunfordPettis (T m)) (hlim : Tendsto T atTop (𝓝 S)) :
    IsDunfordPettis S := by
  apply (isDunfordPettis_iff_weaklyNull S).mpr
  intro x hx
  obtain ⟨C, hC, hbound⟩ := hx.exists_pos_norm_bound
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp hlim (ε / (2 * C)) (by positivity)
  have happrox : ‖S - T m‖ < ε / (2 * C) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hm m le_rfl
  have hmnull := (isDunfordPettis_iff_weaklyNull (T m)).mp (hT m) x hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hmnull (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall : ‖T m (x n)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN n hn
  have happroxC : ‖S - T m‖ * C < ε / 2 := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num) hC)).mp happrox
    nlinarith
  rw [dist_zero_right]
  calc
    ‖S (x n)‖ ≤ ‖(S - T m) (x n)‖ + ‖T m (x n)‖ := by
      simpa only [sub_apply, sub_add_cancel] using
        norm_add_le ((S - T m) (x n)) (T m (x n))
    _ ≤ ‖S - T m‖ * C + ‖T m (x n)‖ := by
      gcongr
      exact ((S - T m).le_opNorm (x n)).trans
        (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _))
    _ < ε := by linarith

/-- The Dunford–Pettis operators form a closed set in operator norm. -/
theorem isClosed_setOf_isDunfordPettis :
    IsClosed {T : E →L[𝕜] F | IsDunfordPettis T} := by
  apply isSeqClosed_iff_isClosed.mp
  intro T S hT hlim
  exact isDunfordPettis_of_tendsto hT hlim

theorem isDunfordPettis_sum {ι : Type*} (s : Finset ι) (T : ι → E →L[𝕜] F)
    (hT : ∀ i ∈ s, IsDunfordPettis (T i)) : IsDunfordPettis (∑ i ∈ s, T i) := by
  change (∑ i ∈ s, T i) ∈ (dunfordPettisSubmodule : Submodule 𝕜 (E →L[𝕜] F))
  exact Submodule.sum_mem _ hT

/-- A summable series of Dunford–Pettis operators has a Dunford–Pettis sum. -/
theorem isDunfordPettis_tsum {ι : Type*} {T : ι → E →L[𝕜] F}
    (hT : ∀ i, IsDunfordPettis (T i)) (hsum : Summable T) :
    IsDunfordPettis (∑' i, T i) := by
  apply isClosed_setOf_isDunfordPettis.mem_of_tendsto hsum.hasSum
  exact Eventually.of_forall (fun s => isDunfordPettis_sum s T (fun i _ => hT i))

/-- In particular, every operator approximable in norm by finite-rank operators
is Dunford–Pettis. -/
theorem isDunfordPettis_of_finiteRank_approximation
    {T : ℕ → E →L[𝕜] F} {S : E →L[𝕜] F}
    (hfinite : ∀ m, FiniteDimensional 𝕜 (T m).range)
    (hlim : Tendsto T atTop (𝓝 S)) : IsDunfordPettis S := by
  apply isDunfordPettis_of_tendsto (T := T) _ hlim
  intro m
  let := hfinite m
  exact isDunfordPettis_of_finiteDimensional_range (T m)

/-- Every compact continuous linear operator is Dunford–Pettis. The proof uses
compactness itself, and imposes no approximation property on either space. -/
theorem isDunfordPettis_of_isCompactOperator (T : E →L[𝕜] F)
    (hT : IsCompactOperator T) : IsDunfordPettis T := by
  intro x a hx
  obtain ⟨K, hK, hTxK⟩ := hT.image_subset_compact_of_bounded hx.isBounded_range
  exact (hx.map T).tendsto_of_isCompact hK (fun n => hTxK ⟨x n, ⟨n, rfl⟩, rfl⟩)

end PL1
