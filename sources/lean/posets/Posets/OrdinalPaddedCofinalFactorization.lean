import Posets.OrdinalColouredCofinalAssembly
import Posets.OrdinalPaddedBandColours
import Posets.OrdinalAmbientCoreBandsSequence

/-! Operator-driven factorization on a countable family of padded ordinal
blocks. Finite colouring, retained derived rank, and cross-mass pruning
produce the local inverses; none is supplied as a hypothesis. The remaining
assumptions describe actual open blocks converging to an endpoint and a
small endpoint row on their union. -/
noncomputable section
namespace Posets
open Set Filter Topology
open ThesisCommon
universe u
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]
  [LocallyCompactSpace K] [T2Space K]
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2400000

theorem ordinalPaddedCofinal_factorization_of_endpoint_bound
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T S : JLMS.CZero 𝕜 K →L[𝕜] JLMS.CZero 𝕜 K)
    (hTS : T + S = ContinuousLinearMap.id 𝕜 _)
    (b : ℕ → Ordinal.{u}) (hb : ∀ i, b i ≠ 0) (habs : ∀ i, 1 + b i = b i)
    (N : ℕ) {ε δ η : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hgap : δ + η < 1 / 2 - 3 * ε) (hN : ‖T‖ + ‖S‖ < N * ε)
    (e : ∀ i, Iic (Ordinal.omega0 ^ (b i * ((2*N+2 : ℕ) : Ordinal))) → K)
    (he : ∀ i, IsOpenEmbedding (e i))
    (hdisj : Pairwise (fun i j => Disjoint (range (e i)) (range (e j))))
    (z : K) (hconv : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, range (e i) ⊆ U)
    (hz : ∀ g : JLMS.CZero 𝕜 K, Function.support g ⊆ ⋃ i, range (e i) →
      ‖T g z‖ ≤ η * ‖g‖ ∧ ‖S g z‖ ≤ η * ‖g‖) :
    ∃ (c : Bool) (k : ℕ → ℕ), StrictMono k ∧
    ∃ J : JLMS.CZeroSum 𝕜 (fun i => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b (k i))) →ₗᵢ[𝕜]
        JLMS.CZero 𝕜 K,
    ∃ R : JLMS.CZero 𝕜 K →L[𝕜]
        JLMS.CZeroSum 𝕜 (fun i => JLMS.OrdinalC 𝕜 (Ordinal.omega0 ^ b (k i))),
      R.comp ((if c then T else S).comp J.toContinuousLinearMap) =
        ContinuousLinearMap.id 𝕜 _ ∧ ‖R‖ ≤ 2 / ((1 / 2 - 3 * ε) - (δ + η)) := by
  classical
  let γ : ℕ → Ordinal.{u} := fun i => b i * ((2*N+2 : ℕ) : Ordinal)
  let θ : ℕ → Ordinal.{u} := fun i => Ordinal.omega0 ^ γ i
  have hθ (i : ℕ) : θ i ∈ ordinalTowerLevel (θ i) (γ i) :=
    ordinalPaddedBand_top_level (b i) (hb i) N
  let x : ∀ i, Iic (θ i) := fun i => ⟨θ i, show θ i ≤ θ i from le_rfl⟩
  have hx (i : ℕ) : x i ∈ ordinalDerived (univ : Set (Iic (θ i))) (γ i) := by
    have ht := hθ i
    change θ i ∈ ordinalDerived (Iic (θ i)) (γ i) at ht
    have hi := ordinalDerived_image_closedEmbedding
      (isClosed_Iic : IsClosed (Iic (θ i))).isClosedEmbedding_subtypeVal univ (γ i)
    rw [image_univ, Subtype.range_coe] at hi
    rw [hi] at ht
    obtain ⟨y, hy, heq⟩ := ht
    have hyx : y = x i := Subtype.ext heq
    exact hyx ▸ hy
  obtain ⟨c, k, hk, n, C, hCc, hCL, hCG, hCr, hCm⟩ :=
    ordinalAmbientCore_sequence_crossMass M hK T S hTS θ γ hθ e he hdisj
      (fun i => ordinalPaddedBandLevels (b i) N)
      (fun i => ordinalPaddedBandLevels_monotone (b i) N) hN hδ γ x hx
  let F : ℕ → Set Ordinal.{u} := fun i =>
    Subtype.val '' ((e (k i)) ⁻¹' C i)
  have hFc (i : ℕ) : IsCompact (F i) :=
    (ordinalAmbientCore_preimage_compact (e (k i)) (he (k i)) (C i) (hCc i)).image
      continuous_subtype_val
  have hFθ (i : ℕ) : F i ⊆ Iic (θ (k i)) := by
    rintro y ⟨v, _, rfl⟩
    exact v.property
  have hFr (i : ℕ) : (ordinalDerived (F i) (γ (k i))).Nonempty := by
    have hr := (ordinalAmbientCore_rank_preimage_iff (e (k i)) (he (k i))
      (C i) (hCG i) (γ (k i)) (x (k i))).mpr (hCr i)
    rw [show F i = Subtype.val '' ((e (k i)) ⁻¹' C i) from rfl,
      ordinalDerived_image_closedEmbedding
        (isClosed_Iic : IsClosed (Iic (θ (k i)))).isClosedEmbedding_subtypeVal]
    exact ⟨_, mem_image_of_mem _ hr⟩
  let G (i : ℕ) := Classical.choice (ordinal_finite_band_exists_geometry (b (k i)) (hb (k i))
    (habs (k i)) N (n i).val (n i).isLt.le (F i) (hFc i) (hFθ i) (hFr i))
  have hF (i : ℕ) : F i ⊆ Subtype.val '' closure
      (ordinalAmbientBandLeaves (hθ (k i)) (e (k i)) (he (k i)) M T S
        (ordinalPaddedBandLevels (b (k i)) N) (n i).val c ε) := by
    rintro y ⟨v, hv, rfl⟩
    refine ⟨v, ?_, rfl⟩
    have hc := hCL i hv
    rw [ordinalAmbientCore_closure_image (e (k i)) (he (k i))] at hc
    exact (he (k i)).injective.mem_set_image.mp hc
  have hds : Pairwise (fun i j => Disjoint (range (e (k i))) (range (e (k j)))) := by
    intro i j hij
    exact hdisj (fun h => hij (hk.injective h))
  have hcv : ∀ U ∈ 𝓝 z, ∀ᶠ i in cofinite, range (e (k i)) ⊆ U :=
    fun U hU => hk.injective.tendsto_cofinite.eventually (hconv U hU)
  have hcross (i : ℕ) (y : K)
      (hy : y ∈ e (k i) '' ((Subtype.val : Iic (θ (k i)) → Ordinal) ⁻¹' F i)) :
      wolfeMass M (wolfeOperatorRow (if c then T else S) y)
        (wolfeCrossUnion (fun j => range (e (k j))) i) ≤ δ := by
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨w, hw, hwv⟩ := hv
    have heq : w = v := Subtype.ext hwv
    exact (hCm i _ (heq ▸ hw)).le
  have hzt (g : JLMS.CZero 𝕜 K)
      (hg : Function.support g ⊆ ⋃ i, range (e (k i))) :
      ‖(if c then T else S) g z‖ ≤ η * ‖g‖ := by
    have hu : Function.support g ⊆ ⋃ i, range (e i) := by
      intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hg hy)
      exact mem_iUnion.mpr ⟨k i, hi⟩
    cases c with
    | false => exact (hz g hu).2
    | true => exact (hz g hu).1
  obtain ⟨J, R, hR, hn⟩ := ordinalColouredCofinal_factorization M T S
    (θ ∘ k) (γ ∘ k)
    (fun i => b (k i) * ((2*(n i).val+2 : ℕ) : Ordinal))
    (fun i => b (k i) * ((2*(n i).val : ℕ) : Ordinal)) (b ∘ k) F
    (fun i => hθ (k i)) (fun i => e (k i)) (fun i => he (k i)) hds
    (fun i => ordinalPaddedBandLevels (b (k i)) N)
    (fun i => ordinalPaddedBandLevels_monotone (b (k i)) N) (fun i => (n i).val) c
    hε hδ.le hη hgap G
    (fun i => ordinalPaddedBandLevels_apply (b (k i)) N (n i).val (by omega))
    (fun i => by
      rw [ordinalPaddedBandLevels_apply (b (k i)) N ((n i).val+1) (by omega)]
      congr 2)
    hF z hcv hcross hzt
  exact ⟨c, k, hk, J, R, hR, hn⟩

end Posets
