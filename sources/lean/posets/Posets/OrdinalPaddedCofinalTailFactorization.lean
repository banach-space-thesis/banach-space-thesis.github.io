import Posets.OrdinalPaddedCofinalFactorization

/-! The endpoint row hypothesis is discharged by summability on disjoint
blocks. The resulting uniform factorization is constructed from the
operator splitting and actual convergent open ordinal blocks alone. -/
noncomputable section
namespace Posets
open Set Filter Topology
universe u
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

theorem ordinalPaddedCofinal_factorization
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (b : ℕ → Ordinal.{u}) (hb : ∀ i, b i ≠ 0) (habs : ∀ i, 1 + b i = b i)
    (N : ℕ) {ε δ η : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hη : 0 < η)
    (hgap : δ + η < 1 / 2 - 3 * ε) (hN : ‖T‖ + ‖S‖ < N * ε)
    (e : ∀ i, Iic (Ordinal.omega0 ^ (b i * ((2*N+2 : ℕ) : Ordinal))) → K)
    (he : ∀ i, IsOpenEmbedding (e i))
    (hdisj : Pairwise (fun i j => Disjoint (range (e i)) (range (e j))))
    (z : K) (hconv : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, range (e i) ⊆ U) :
    ∃ (c : Bool) (k : ℕ → ℕ), StrictMono k ∧
    ∃ J : JLMS.CZeroSum 𝕜 (fun i => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b (k i))) →ₗᵢ[𝕜]
        JLMS.CZero 𝕜 K,
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜]
        JLMS.CZeroSum 𝕜 (fun i => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b (k i))),
      R.comp ((if c then T else S).comp J.toContinuousLinearMap) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 2 / ((1 / 2 - 3 * ε) - (δ + η)) := by
  obtain ⟨mT, hmT⟩ := wolfeMass_endpoint_disjoint_tail_small M T z
    (fun i => range (e i)) hdisj hη
  obtain ⟨mS, hmS⟩ := wolfeMass_endpoint_disjoint_tail_small M S z
    (fun i => range (e i)) hdisj hη
  let m := max mT mS
  have hmTle : mT ≤ m := le_max_left _ _
  have hmSle : mS ≤ m := le_max_right _ _
  have hinj : Function.Injective (fun i : ℕ => i+m) := fun _ _ h => Nat.add_right_cancel h
  have hd : Pairwise (fun i j => Disjoint (range (e (i+m))) (range (e (j+m)))) := by
    intro i j hij
    exact hdisj (fun h => hij (hinj h))
  have hc : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, range (e (i+m)) ⊆ U :=
    fun U hU => hinj.tendsto_cofinite.eventually (hconv U hU)
  have hz (g : JLMS.CZero 𝕜 K)
      (hg : Function.support g ⊆ ⋃ i, range (e (i+m))) :
      ‖T g z‖ ≤ η * ‖g‖ ∧ ‖S g z‖ ≤ η * ‖g‖ := by
    constructor
    · apply hmT g
      intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hg hy)
      apply mem_iUnion.mpr
      refine ⟨i+(m-mT), ?_⟩
      have heq : i + (m-mT) + mT = i+m := by omega
      exact (congrArg (fun n : ℕ => y ∈ range (e n)) heq).mpr hi
    · apply hmS g
      intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hg hy)
      apply mem_iUnion.mpr
      refine ⟨i+(m-mS), ?_⟩
      have heq : i + (m-mS) + mS = i+m := by omega
      exact (congrArg (fun n : ℕ => y ∈ range (e n)) heq).mpr hi
  obtain ⟨c, k, hk, J, R, hR, hn⟩ :=
    ordinalPaddedCofinal_factorization_of_endpoint_bound M hK T S hTS
      (fun i => b (i+m)) (fun i => hb (i+m)) (fun i => habs (i+m)) N
      hε hδ hη.le hgap hN (fun i => e (i+m)) (fun i => he (i+m)) hd z hc hz
  exact ⟨c, fun i => k i+m, fun _ _ hij => Nat.add_lt_add_right (hk hij) m,
    J, R, hR, hn⟩

end Posets
