import CKEUPFP.Definitions
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Tactic.Linarith

/-!
# Density of finite-rank continuous vector-valued functions

A finite partition of unity approximates each continuous function by a finite
sum of scalar continuous functions times fixed vectors. This is the density
input for lifting scalar continuous-function-space isomorphisms to vector
range spaces in the Milutin reduction.
-/

noncomputable section

namespace CKEUPFP

variable (𝕜 K E : Type*) [RCLike 𝕜] [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A scalar continuous function multiplied by one fixed range vector. -/
def scalarVector (g : C(K, 𝕜)) (x : E) : C(K, E) :=
  ⟨fun t => g t • x, g.continuous.smul continuous_const⟩

/-- The algebraic finite-rank subspace of `C(K,E)`. -/
def VectorFiniteRank : Submodule 𝕜 C(K, E) :=
  Submodule.span 𝕜 {f | ∃ g : C(K, 𝕜), ∃ x : E, ∀ t, f t = g t • x}

variable {𝕜 K E}

@[simp] theorem scalarVector_apply (g : C(K, 𝕜)) (x : E) (t : K) :
    scalarVector 𝕜 K E g x t = g t • x := rfl

theorem scalarVector_mem (g : C(K, 𝕜)) (x : E) :
    scalarVector 𝕜 K E g x ∈ VectorFiniteRank 𝕜 K E :=
  Submodule.subset_span ⟨g, x, fun _ => rfl⟩

variable [CompactSpace K] [T2Space K]

/-- A finite partition of unity gives a finite-rank approximation in the
supremum norm. There is no approximation-property hypothesis on `E`. -/
theorem exists_vectorFiniteRank_approx (f : C(K, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ VectorFiniteRank 𝕜 K E, ‖g - f‖ < ε := by
  classical
  let U : K → Set K := fun x => {y | ‖f y - f x‖ < ε / 2}
  have hU : ∀ x, IsOpen (U x) := fun x =>
    isOpen_lt (f.continuous.sub continuous_const).norm continuous_const
  have hcover : (Set.univ : Set K) ⊆ ⋃ x, U x := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, by simpa [U] using half_pos hε⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hcover' : (Set.univ : Set K) ⊆ ⋃ i : s, U i := by
    intro y hy
    obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (hs hy)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hiy⟩
  obtain ⟨p, hp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun i : s => U i) (fun i => hU i)
    (locallyFinite_of_finite _) hcover'
  let φ : s → C(K, 𝕜) := fun i =>
    ⟨fun t => (p i t : 𝕜), RCLike.continuous_ofReal.comp (p i).continuous⟩
  let g : C(K, E) := ∑ i : s, scalarVector 𝕜 K E (φ i) (f i)
  have hg : g ∈ VectorFiniteRank 𝕜 K E :=
    Submodule.sum_mem _ (fun i _ => scalarVector_mem (φ i) (f i))
  have hsum (t : K) : ∑ i : s, p i t = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one (Set.mem_univ t)
  have hsum𝕜 (t : K) : ∑ i : s, (p i t : 𝕜) = 1 := by
    simpa using congrArg (fun r : ℝ => (r : 𝕜)) (hsum t)
  have hpoint (t : K) : ‖(g - f) t‖ ≤ ε / 2 := by
    have heq : (g - f) t = ∑ i : s, (p i t : 𝕜) • (f i - f t) := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
        scalarVector_apply, φ, ContinuousMap.coe_mk, smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hsum𝕜, one_smul]
    rw [heq]
    calc
      ‖∑ i : s, (p i t : 𝕜) • (f i - f t)‖ ≤
          ∑ i : s, ‖(p i t : 𝕜) • (f i - f t)‖ := norm_sum_le _ _
      _ ≤ ∑ i : s, p i t * (ε / 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (p.nonneg i t)]
        by_cases hpt : p i t = 0
        · simp [hpt]
        · have htU : t ∈ U i := hp i (subset_closure hpt)
          have hdist : ‖f i - f t‖ ≤ ε / 2 := by
            rw [norm_sub_rev]
            exact htU.le
          exact mul_le_mul_of_nonneg_left hdist (p.nonneg i t)
      _ = ε / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hnorm : ‖g - f‖ ≤ ε / 2 :=
    (ContinuousMap.norm_le _ (half_pos hε).le).mpr hpoint
  exact ⟨g, hg, hnorm.trans_lt (half_lt_self hε)⟩

/-- Finite sums of scalar continuous functions times fixed vectors are dense. -/
theorem vectorFiniteRank_dense : Dense (VectorFiniteRank 𝕜 K E : Set C(K, E)) := by
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hgf⟩ := exists_vectorFiniteRank_approx (𝕜 := 𝕜) f hε
  exact ⟨g, hg, by simpa only [dist_eq_norm, norm_sub_rev] using hgf⟩

end CKEUPFP
