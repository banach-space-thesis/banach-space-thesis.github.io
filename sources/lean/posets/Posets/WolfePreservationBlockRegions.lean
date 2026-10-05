import Posets.WolfePreservationBlockCompact

/-! Uniform compact clopen regions for a disjoint family of source blocks.
The constants come from one fixed identity factorization and do not depend
on the source block or its Cantor--Bendixson rank. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 K L X : Type*} [RCLike 𝕜] [TopologicalSpace K] [TopologicalSpace L]
  [LocallyCompactSpace K] [T2Space K] [CompactSpace L]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem wolfeFactorizationLift_compact_block_regions
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (T : JLMS.CZero 𝕜 K →L[𝕜] X) (R : X →L[𝕜] JLMS.CZero 𝕜 L)
    (S : JLMS.CZero 𝕜 L →L[𝕜] JLMS.CZero 𝕜 K)
    (hfactor : R.comp (T.comp S) = ContinuousLinearMap.id 𝕜 (JLMS.CZero 𝕜 L))
    (c : 𝕜) (hc : c ≠ 0) (hn : ‖c‖ * ‖R‖ ≤ 1)
    (V : ℕ → Set L) (hV : ∀ n, IsClopen (V n))
    (hd : Pairwise fun n m => Disjoint (V n) (V m)) :
    ∃ H : ℕ → Set K,
      (∀ n, IsClopen (H n) ∧ IsCompact (H n)) ∧
      (∀ n, H n ⊆ wolfeBlockOpen S (V n) (hV n)
        ((‖c‖ / (2 * (‖T‖ + 1))) / 2)) ∧
      (∀ n x, x ∈ V n → ‖c‖ / (4 * (‖S‖ + 1)) <
        wolfeMass M (wolfeFactorizationLift T R c x) (H n)) ∧
      ∀ (s : Finset ℕ) (y : K), (∀ n ∈ s, y ∈ H n) →
        (s.card : ℝ) * ((‖c‖ / (2 * (‖T‖ + 1))) / 2) ≤ ‖S‖ := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hgap : ‖c‖ / (4 * (‖S‖ + 1)) < ‖c‖ / (2 * (‖S‖ + 1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [norm_nonneg S]
  have hex (n : ℕ) : ∃ H : Set K, IsClopen H ∧ IsCompact H ∧
      H ⊆ wolfeBlockOpen S (V n) (hV n) ((‖c‖ / (2 * (‖T‖ + 1))) / 2) ∧
      ∀ x ∈ V n, ‖c‖ / (4 * (‖S‖ + 1)) <
        wolfeMass M (wolfeFactorizationLift T R c x) H := by
    apply wolfe_exists_compact_clopen_uniform_mass M hK (wolfeFactorizationLift T R c)
      (wolfeFactorizationLift_continuous T R c) (hV n).isClosed.isCompact
      (wolfeBlockOpen_isOpen S (V n) (hV n) _)
    intro x hx
    exact hgap.trans_le (wolfeFactorizationLift_block_open_mass M T R S hfactor c hc hn
      (V n) (hV n) x hx)
  choose H hH hHc hHU hmass using hex
  refine ⟨H, fun n => ⟨hH n, hHc n⟩, hHU, hmass, ?_⟩
  intro s y hy
  exact wolfeBlockOpen_finite_overlap S V hV hd _ s y
    (fun n hn => hHU n (hy n hn))

end Posets
