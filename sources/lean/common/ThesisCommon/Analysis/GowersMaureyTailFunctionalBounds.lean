import ThesisCommon.Analysis.GowersMaureyFiniteOrbitWitness

/-! Tail support estimates on the actual completion. Finite spread images of
nonzero block tests eventually lie beyond every fixed cutoff. Conversely all
dual-unit finite functionals beyond a cutoff uniformly vanish on a fixed
completed vector as the cutoff increases. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem spread_mem_afterCutoff {x : C00 𝕜} (K m n : ℕ)
    (hx : x ∈ afterCutoff (K+m)) : spread m n x ∈ afterCutoff K := by
  intro j hj
  rw [spread_apply]
  split_ifs
  · exact hx _ (by omega)
  · rfl

theorem BlockTestSequence.eventually_finite_spreads_after {D : ConstructionData 𝕜}
    {Y : Submodule 𝕜 (ShiftSpace D)} (u : BlockTestSequence D Y)
    (hne : ∀ i, u.vector i ≠ 0) (s : Finset (ℕ × ℕ)) (K : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ z ∈ s, spread z.1 z.2 (u.vector i) ∈ afterCutoff K := by
  apply eventually_atTop.mpr
  refine ⟨K+s.sup Prod.fst+1,?_⟩
  intro i hi z hz
  apply spread_mem_afterCutoff
  intro j hj
  apply Finsupp.notMem_support_iff.mp
  intro hji
  have hh := block_index_le_support u.vector u.successive hne i j hji
  have hzle := Finset.le_sup (f := Prod.fst) hz
  omega

@[simp] theorem completedPairing_basisVector (D : ConstructionData 𝕜)
    (a : C00 𝕜) (i : ℕ) : completedPairing D a (basisVector D i) = a i := by
  simp [basisVector, PreSpace.single, pairing]

theorem completedPairing_initialSum_eq_zero (D : ConstructionData 𝕜)
    {a : C00 𝕜} {K : ℕ} (ha : a ∈ afterCutoff K) (x : ShiftSpace D) :
    completedPairing D a (initialSum D (K+1) x) = 0 := by
  rw [initialSum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul, completedPairing_basisVector, ha i (by
    have hh := Finset.mem_range.mp hi
    omega), smul_zero]

theorem completedPairing_le_tail_norm (D : ConstructionData 𝕜)
    {a : C00 𝕜} {K : ℕ} (ha : a ∈ afterCutoff K)
    (hu : DualUnit (implicitNorm D) a) (x : ShiftSpace D) :
    ‖completedPairing D a x‖ ≤ ‖x-initialSum D (K+1) x‖ := by
  have he : completedPairing D a (x-initialSum D (K+1) x) = completedPairing D a x := by
    rw [map_sub, completedPairing_initialSum_eq_zero D ha, sub_zero]
  rw [← he]
  exact completedPairing_norm_bound hu _

theorem eventually_tail_dualUnit_small (D : ConstructionData 𝕜) (x : ShiftSpace D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, ∀ a : C00 𝕜, a ∈ afterCutoff K →
      DualUnit (implicitNorm D) a → ‖completedPairing D a x‖ < ε := by
  have h := ((tendsto_const_nhds (x := x)).sub
    ((initialSum_tendsto D x).comp (tendsto_add_atTop_nat 1))).norm
  have hsmall : ∀ᶠ K : ℕ in atTop, ‖x-initialSum D (K+1) x‖ < ε := by
    apply h.eventually_lt_const
    simpa using hε
  filter_upwards [hsmall] with K hK
  intro a ha hu
  exact (completedPairing_le_tail_norm D ha hu x).trans_lt hK

end ThesisCommon.GowersMaurey
