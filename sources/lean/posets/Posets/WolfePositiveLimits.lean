import Posets.AlspachCounterexampleMassCalculus
import Posets.WolfeFamilies
import JLMS.ScatteredTopology

/-! Closure containment retains positive row mass at weak-star limits.
The compact clopen cutoff is one on every child open set and lies inside the
parent. Positivity then lets its continuous evaluation carry the mass bound
to the limit, over both real and complex scalar fields. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

theorem wolfe_exists_compact_clopen_between [LocallyCompactSpace K] [T2Space K]
    (hK : JLMS.IsScattered K) {C G : Set K} (hC : IsCompact C)
    (hG : IsOpen G) (hCG : C ⊆ G) :
    ∃ H : Set K, IsClopen H ∧ IsCompact H ∧ C ⊆ H ∧ H ⊆ G := by
  classical
  choose U hcl hc hx hsub using fun x : C =>
    JLMS.exists_compact_clopen_subset hK hG (hCG x.property)
  have hcover : C ⊆ ⋃ x : C, U x := fun x hxC =>
    mem_iUnion.mpr ⟨⟨x, hxC⟩, hx ⟨x, hxC⟩⟩
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover U (fun x => (hcl x).isOpen) hcover
  exact ⟨⋃ x ∈ s, U x, isClopen_biUnion_finset (fun x _ => hcl x),
    s.isCompact_biUnion (fun x _ => hc x), hs,
    iUnion_subset fun x => iUnion_subset fun _ => hsub x⟩

omit [TopologicalSpace K] in
theorem wolfe_probability_eval_indicator (q : AlspachProbability K) (H : Set K) :
    q.eval (fun k => if k ∈ H then (1 : 𝕜) else 0) = (q.mass H : 𝕜) := by
  classical
  induction q with
  | point k => by_cases hk : k ∈ H <;> simp [AlspachProbability.mass, hk]
  | average p q hp hq =>
      simp only [AlspachProbability.eval_average, AlspachProbability.mass, hp, hq,
        RCLike.ofReal_mul, RCLike.ofReal_add, RCLike.ofReal_div, RCLike.ofReal_one,
        RCLike.ofReal_ofNat]

theorem wolfe_probability_mass_le_of_weakStar_limit
    [LocallyCompactSpace K] [T2Space K]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (q : ℕ → AlspachProbability K) (p : AlspachProbability K)
    (hconv : Tendsto (fun n => StrongDual.toWeakDual (M.representation.symm (q n).vector))
      atTop (𝓝 (StrongDual.toWeakDual (M.representation.symm p.vector))))
    (U : ℕ → Set K) {G : Set K} (hG : IsOpen G)
    (hcompact : IsCompact (closure (⋃ n, U n))) (hclosure : closure (⋃ n, U n) ⊆ G)
    {ε : ℝ} (hmass : ∀ n, ε ≤ (q n).mass (U n)) : ε ≤ p.mass G := by
  obtain ⟨H, hH, hHc, hCH, hHG⟩ := wolfe_exists_compact_clopen_between hK hcompact hG hclosure
  let f : JLMS.CZero 𝕜 K := JLMS.clopenIndicator H hH hHc
  have heval (r : AlspachProbability K) :
      RCLike.re (StrongDual.toWeakDual (M.representation.symm r.vector) f) = r.mass H := by
    change RCLike.re (M.representation.symm r.vector f) = _
    rw [r.representation_symm_apply M f]
    have hf : (f : K → 𝕜) = fun k => if k ∈ H then 1 else 0 := by
      funext k
      exact JLMS.clopenIndicator_apply H hH hHc k
    rw [hf, wolfe_probability_eval_indicator, RCLike.ofReal_re]
  have ht : Tendsto (fun n => (q n).mass H) atTop (𝓝 (p.mass H)) := by
    have h := (RCLike.continuous_re.continuousAt.tendsto.comp
      ((WeakDual.eval_continuous f).continuousAt.tendsto.comp hconv))
    change Tendsto (fun n => RCLike.re
      (StrongDual.toWeakDual (M.representation.symm (q n).vector) f)) atTop
      (𝓝 (RCLike.re (StrongDual.toWeakDual (M.representation.symm p.vector) f))) at h
    simpa only [heval] using h
  have hεH : ε ≤ p.mass H := ge_of_tendsto ht (Eventually.of_forall fun n =>
    (hmass n).trans ((q n).mass_mono ((subset_iUnion U n).trans (subset_closure.trans hCH))))
  exact hεH.trans (p.mass_mono hHG)

theorem wolfe_probability_mass_le_of_children
    [CompactSpace K] [T2Space K]
    (M : JLMS.AtomicDualModel 𝕜 K) (hK : JLMS.IsScattered K)
    (q : ℕ → AlspachProbability K) (p : AlspachProbability K)
    (hconv : Tendsto (fun n => StrongDual.toWeakDual (M.representation.symm (q n).vector))
      atTop (𝓝 (StrongDual.toWeakDual (M.representation.symm p.vector))))
    (U : ℕ → Set K) {G : Set K} (hG : IsOpen G)
    (hclosure : closure (⋃ n, U n) ⊆ G) {ε : ℝ}
    (hmass : ∀ n, ε ≤ (q n).mass (U n)) : ε ≤ p.mass G :=
  wolfe_probability_mass_le_of_weakStar_limit M hK q p hconv U hG
    isClosed_closure.isCompact hclosure hmass

end Posets
