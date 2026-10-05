import ThesisCommon.Analysis.GowersMaureyOrbitCounterexamples
import ThesisCommon.Analysis.GowersMaureyTailFunctionalBounds

/-! Actual finite tail witnesses along a counterexample block sequence.
The operator remains defined on the original subspace. Every fixed finite
spread orbit has a dual-unit witness sufficiently far along the sequence;
the images need only be approximated, never assumed finitely supported. -/
noncomputable section
open Filter
namespace ThesisCommon.GowersMaurey
variable {𝕜 : Type*} [RCLike 𝕜]

theorem BlockTestSequence.eventually_finite_orbit_witnesses
    {D : ConstructionData 𝕜} {Y : Submodule 𝕜 (ShiftSpace D)}
    (u : BlockTestSequence D Y) (hne : ∀ i, u.vector i ≠ 0)
    (T : Y →L[𝕜] ShiftSpace D) (q : ℕ → ℕ) (hq : StrictMono q)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ i, ∀ z ∈ spreadVectorOrbit D (u.vector i) (q i),
      ε ≤ ‖T (u.inSubspace i)-z‖) (r K : ℕ) (hr : 0 < r) :
    ∀ᶠ i : ℕ in atTop,
      (∀ z ∈ spreadParameterSquare r, spread z.1 z.2 (u.vector i) ∈ afterCutoff K) ∧
      ∃ a : C00 𝕜, a ∈ afterCutoff K ∧ DualUnit (implicitNorm D) a ∧ a ≠ 0 ∧
        ε/4 < RCLike.re (completedPairing D a (T (u.inSubspace i))) ∧
        ∀ z ∈ spreadParameterSquare r,
          ‖pairing a (spread z.1 z.2 (u.vector i))‖ ≤ ‖T‖/r := by
  have hhead := (u.tendsto_initialSum_operator_zero T (K+1)).norm.eventually_lt_const
    (by simpa only [norm_zero] using (show 0 < ε/8 by positivity))
  filter_upwards [u.eventually_finite_spreads_after hne (spreadParameterSquare r) K,
    eventually_spread_orbit_separated u T q hq hsep r,hhead] with i hi hs hhi
  have hs' : ∀ w ∈ finiteAbsoluteConvexOrbit (𝕜 := 𝕜)
      (fun z : spreadParameterSquare r =>
        denseEmbedding D (spread z.val.1 z.val.2 (u.vector i))) r,
      ε ≤ ‖T (u.inSubspace i)-w‖ := by
    change ∀ w ∈ finiteParameterOrbit (𝕜 := 𝕜)
      (fun z : ℕ × ℕ => denseEmbedding D (spread z.1 z.2 (u.vector i)))
      (spreadParameterSquare r) r, _ at hs
    rw [finiteParameterOrbit_eq] at hs
    exact hs
  obtain ⟨a,haK,hau,haz,hav⟩ := exists_finite_tail_orbit_witness D
    (fun z : spreadParameterSquare r => spread z.val.1 z.val.2 (u.vector i))
    (T (u.inSubspace i)) K (fun z => hi z.val z.property)
    (show 0 < (r : ℝ) by exact_mod_cast hr) hε hhi hs'
  have haz' : ε/4 < RCLike.re (completedPairing D a (T (u.inSubspace i))) := by
    linarith
  refine ⟨hi,a,haK,hau,?_,haz',?_⟩
  · intro ha0
    have hh : RCLike.re (completedPairing D a (T (u.inSubspace i))) = 0 := by
      simp [ha0]
    rw [hh] at haz'
    linarith
  · intro z hz
    apply (hav ⟨z,hz⟩).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
    exact (T.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg T)
      (u.norm_inSubspace_le_one i))

end ThesisCommon.GowersMaurey
