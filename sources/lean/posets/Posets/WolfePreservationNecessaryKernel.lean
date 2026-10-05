import Posets.WolfePreservationNecessaryAtomic
import Posets.WolfeNorming

/-! Source regions pulled back through the variation of the genuine adjoint
kernel. Unlike the scalar image of an indicator, these regions are monotone in
the source set. Disjoint source regions have uniformly bounded overlap, even
when they belong to different levels of a source tree. -/

noncomputable section
open Set Filter Topology
namespace Posets
variable {𝕜 K L : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]

def wolfeKernelRegion (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) (V : Set L) (δ : ℝ) : Set K :=
  {y | δ < wolfeMass N (weakStarAdjoint S (wolfeDirac y)) V}

theorem wolfeKernelRegion_isOpen [LocallyCompactSpace L] [T2Space L]
    (N : JLMS.AtomicDualModel 𝕜 L) (hL : JLMS.IsScattered L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    {V : Set L} (hV : IsOpen V) (δ : ℝ) : IsOpen (wolfeKernelRegion N S V δ) :=
  (isOpen_wolfeMass_gt N hL hV δ).preimage
    ((weakStarAdjoint_continuous S).comp wolfeDirac_continuous)

theorem wolfeKernelRegion_mono (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    {V W : Set L} (hVW : V ⊆ W) (δ : ℝ) :
    wolfeKernelRegion N S V δ ⊆ wolfeKernelRegion N S W δ := by
  intro y hy
  exact hy.trans_le (wolfeMass_mono N _ hVW)

theorem wolfeKernelRegion_finite_budget {I : Type*}
    (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (V : I → Set L) (hV : Pairwise (fun i j => Disjoint (V i) (V j)))
    (y : K) {δ : ℝ} (s : Finset I)
    (hs : ∀ i ∈ s, y ∈ wolfeKernelRegion N S (V i) δ) :
    (s.card : ℝ) * δ ≤ ‖S‖ := by
  have hsum : (s.card : ℝ) * δ ≤
      ∑ i ∈ s, wolfeMass N (weakStarAdjoint S (wolfeDirac y)) (V i) := by
    simpa using Finset.sum_le_sum (s := s)
      (f := fun _ => δ) (g := fun i => wolfeMass N (weakStarAdjoint S (wolfeDirac y)) (V i))
      (fun i hi => (hs i hi).le)
  have hnorm : ‖WeakDual.toStrongDual (weakStarAdjoint S (wolfeDirac y))‖ ≤ ‖S‖ := by
    rw [← N.representation.norm_map]
    exact wolfeAtomicCrossRow_norm_le N S y
  exact hsum.trans ((wolfeMass_finset_sum_le N _ V hV s).trans hnorm)

theorem wolfeKernelRegion_uniform_finite_overlap
    (N : JLMS.AtomicDualModel 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ {I : Type*} (V : I → Set L),
      Pairwise (fun i j => Disjoint (V i) (V j)) →
      ∀ y : K, ∀ s : Finset I,
        (∀ i ∈ s, y ∈ wolfeKernelRegion N S (V i) δ) → s.card ≤ m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (‖S‖ / δ)
  have hmpos : 0 < m := by
    have : 0 ≤ ‖S‖ / δ := by positivity
    exact_mod_cast this.trans_lt hm
  refine ⟨m, hmpos, ?_⟩
  intro I V hV y s hs
  have hb := wolfeKernelRegion_finite_budget N S V hV y s hs
  have hlt : (s.card : ℝ) < m := by
    apply (mul_lt_mul_iff_left₀ hδ).mp
    exact hb.trans_lt ((div_lt_iff₀ hδ).mp hm)
  exact (by exact_mod_cast hlt : s.card < m).le

theorem wolfeFactorizationLift_kernelRegion_mass
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : JLMS.AtomicDualModel 𝕜 K) (N : JLMS.AtomicDualModel 𝕜 L)
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    {V : Set L} {x : L} (hx : x ∈ V) :
    ‖c‖ / (2 * (‖S‖ + 1)) ≤ wolfeMass M (wolfeFactorizationLift T R c x)
      (wolfeKernelRegion N S V (‖c‖ / (4 * (‖T‖ + 1)))) := by
  apply (wolfeFactorizationLift_large_coordinate_mass M N T R S hfactor c hc hn x).trans
  apply wolfeMass_mono M _
  intro y hy
  have hcoord : ‖wolfeAtomicCrossRow N S y x‖ ≤
      wolfeMass N (weakStarAdjoint S (wolfeDirac y)) V := by
    change ‖N.representation (WeakDual.toStrongDual (weakStarAdjoint S (wolfeDirac y))) x‖ ≤ _
    rw [← wolfeMass_singleton N (weakStarAdjoint S (wolfeDirac y)) x]
    exact wolfeMass_mono N _ (singleton_subset_iff.mpr hx)
  have hhalf : ‖c‖ / (4 * (‖T‖ + 1)) < ‖c‖ / (2 * (‖T‖ + 1)) := by
    apply div_lt_div_of_pos_left (norm_pos_iff.mpr hc) (by positivity)
    nlinarith [norm_nonneg T]
  exact hhalf.trans_le (hy.trans hcoord)

end Posets
