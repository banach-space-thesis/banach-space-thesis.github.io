import ThesisCommon.Analysis.RCLikeEllOneSchur
import ThesisCommon.Analysis.CountableCoordinateSupport
import ThesisCommon.WeakCompact
import Mathlib.Topology.Sequences

/-! Weakly compact subsets of scalar ℓ₁(Γ) are norm compact, over either
real or complex scalars and with arbitrary Γ. For each sequence, the union
of its coordinate supports is countable. The corresponding weakly closed
coordinate subspace cuts out a compact, first-countable subspace. Schur's
theorem upgrades its convergent subsequence to convergence in norm.
-/
noncomputable section
open Set Filter Topology TopologicalSpace
namespace ThesisCommon
variable {𝕜 Γ : Type*} [RCLike 𝕜]

/-- Coordinates on a countable support set metrize each weakly compact
subspace supported there. Only first countability is needed below. -/
theorem weakScalarEllOne_compact_supported_firstCountable
    {K : Set (WeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1))} (hK : IsCompact K)
    (Δ : Set Γ) (hΔ : Δ.Countable)
    (hsupp : ∀ x ∈ K, ∀ γ ∉ Δ,
      (toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm x γ = 0) :
    FirstCountableTopology K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Countable Δ := hΔ.to_subtype
  let c : K → (Δ → 𝕜) := fun x γ =>
    (toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm x.val γ.val
  have hc : Continuous c := by
    apply continuous_pi
    intro γ
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 (lp (fun _ : Γ => 𝕜) 1)).flip
      (lpCoordinate 1 γ.val)).comp continuous_subtype_val
  have hinj : Function.Injective c := by
    intro x y hxy
    apply Subtype.ext
    apply (toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm.injective
    apply lp.ext
    funext γ
    by_cases hγ : γ ∈ Δ
    · exact congrFun hxy ⟨γ, hγ⟩
    · rw [hsupp x.val x.property γ hγ, hsupp y.val y.property γ hγ]
  exact (hc.isClosedEmbedding hinj).isEmbedding.firstCountableTopology

/-- The arbitrary-index real/complex version of weak compactness plus
Schur implying norm compactness. No sequential weak-compactness theorem
is assumed: the required subsequence is extracted on its countable support. -/
theorem isCompact_norm_of_weakScalarEllOne
    {K : Set (WeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1))} (hK : IsCompact K) :
    IsCompact ((toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm '' K) := by
  classical
  apply IsSeqCompact.isCompact
  intro u hu
  let Δ : Set Γ := ⋃ n : ℕ, Function.support (u n)
  have hΔ : Δ.Countable := Set.countable_iUnion fun n =>
    lp_countable_support (by norm_num) (by norm_num) (u n)
  let L : Set (WeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)) :=
    K ∩ {x | ∀ γ ∉ Δ, (toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm x γ = 0}
  have hclosed : IsClosed {x : WeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1) |
      ∀ γ ∉ Δ, (toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm x γ = 0} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro γ
    apply isClosed_iInter
    intro _
    exact isClosed_eq
      (WeakBilin.eval_continuous (topDualPairing 𝕜 (lp (fun _ : Γ => 𝕜) 1)).flip
        (lpCoordinate 1 γ)) continuous_const
  have hL : IsCompact L := hK.inter_right hclosed
  have huL (n : ℕ) : toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1) (u n) ∈ L := by
    constructor
    · obtain ⟨x, hx, heq⟩ := hu n
      rw [← heq]
      simpa using hx
    · intro γ hγ
      change u n γ = 0
      by_contra hn
      exact hγ (Set.mem_iUnion.mpr ⟨n, hn⟩)
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  letI : FirstCountableTopology L :=
    weakScalarEllOne_compact_supported_firstCountable hL Δ hΔ (fun x hx => hx.2)
  let v : ℕ → L := fun n => ⟨toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1) (u n), huL n⟩
  obtain ⟨a, r, hr, ha⟩ := CompactSpace.tendsto_subseq v
  let z := (toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm a.val
  have hweak : ∀ φ : lp (fun _ : Γ => 𝕜) 1 →L[𝕜] 𝕜,
      Tendsto (fun n => φ (u (r n) - z)) atTop (𝓝 0) := by
    intro φ
    have hc : Continuous (fun x : L =>
        φ ((toWeakSpace 𝕜 (lp (fun _ : Γ => 𝕜) 1)).symm x.val)) :=
      (WeakBilin.eval_continuous (topDualPairing 𝕜 (lp (fun _ : Γ => 𝕜) 1)).flip φ).comp
        continuous_subtype_val
    have ht := ((hc.tendsto a).comp ha).sub (tendsto_const_nhds (x := φ z))
    simpa only [v, z, Function.comp_def, LinearEquiv.symm_apply_apply, map_sub, sub_self]
      using ht
  refine ⟨z, ⟨a.val, a.property.1, rfl⟩, r, hr, ?_⟩
  have ht := (scalar_ellOne_schur_tendsto (fun n => u (r n) - z) hweak).add
    (tendsto_const_nhds (x := z))
  simpa only [sub_add_cancel, zero_add, Function.comp_def] using ht

end ThesisCommon
