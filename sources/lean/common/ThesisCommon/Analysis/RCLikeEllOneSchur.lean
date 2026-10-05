import ThesisCommon.Analysis.RCLikeEllOneSchurBlocks

/-! Schur's theorem for scalar ell-one over either real or complex scalars,
with arbitrary coordinate index set. The test functional is genuinely linear
over the supplied scalar field. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ThesisCommon
variable {𝕜 I : Type*} [RCLike 𝕜]
attribute [local instance] Classical.decEq Classical.propDecidable

private def scalarSchurPhase (z : 𝕜) : 𝕜 :=
  (RCLike.exists_norm_eq_mul_self z).choose

private theorem scalarSchurPhase_norm (z : 𝕜) : ‖scalarSchurPhase z‖ = 1 :=
  (RCLike.exists_norm_eq_mul_self z).choose_spec.1

private theorem scalarSchurPhase_mul (z : 𝕜) : scalarSchurPhase z * z = (‖z‖ : 𝕜) :=
  (RCLike.exists_norm_eq_mul_self z).choose_spec.2.symm

private def scalarBlockPhase (u : ℕ → lp (fun _ : I => 𝕜) 1)
    (B : ℕ → Finset I) (i : I) : 𝕜 :=
  if h : ∃ n, i ∈ B n then scalarSchurPhase (u h.choose i) else 0

private theorem scalarBlockPhase_bound (u : ℕ → lp (fun _ : I => 𝕜) 1)
    (B : ℕ → Finset I) (i : I) : ‖scalarBlockPhase u B i‖ ≤ 1 := by
  unfold scalarBlockPhase
  split_ifs <;> simp [scalarSchurPhase_norm]

private theorem scalarBlockPhase_mul (u : ℕ → lp (fun _ : I => 𝕜) 1)
    (B : ℕ → Finset I) (hB : Pairwise (fun m n => Disjoint (B m) (B n)))
    (n : ℕ) (i : I) (hi : i ∈ B n) :
    scalarBlockPhase u B i * u n i = (‖u n i‖ : 𝕜) := by
  have h : ∃ m, i ∈ B m := ⟨n, hi⟩
  have heq : h.choose = n := by
    by_contra hn
    exact Finset.disjoint_left.mp (hB hn) h.choose_spec hi
  rw [scalarBlockPhase, dif_pos h, heq, scalarSchurPhase_mul]

/-- The real part of one bounded scalar-linear test detects every member
of a suitable subsequence of a coordinatewise null sequence. -/
theorem scalar_ellOne_subsequence_norm_test (u : ℕ → lp (fun _ : I => 𝕜) 1)
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ φ : lp (fun _ : I => 𝕜) 1 →L[𝕜] 𝕜,
      ∀ n, ‖u (r n)‖ - 2 * ε < RCLike.re (φ (u (r n))) := by
  obtain ⟨r, hr, B, hB, herr⟩ := scalar_ellOne_disjoint_finite_blocks u hu hε
  let v := fun n => u (r n)
  let b := scalarBlockPhase v B
  have hb := scalarBlockPhase_bound v B
  let φ := scalarEllOneTest b hb
  refine ⟨r, hr, φ, fun n => ?_⟩
  let w := ∑ i ∈ B n, lp.single 1 i (v n i)
  have hw : φ w = ((∑ i ∈ B n, ‖v n i‖ : ℝ) : 𝕜) := by
    simp only [w, map_sum, φ, scalarEllOneTest_single]
    exact Finset.sum_congr rfl (fun i hi => scalarBlockPhase_mul v B hB n i hi)
  have ht := (abs_le.mp ((RCLike.abs_re_le_norm (φ (v n - w))).trans
    (scalarEllOneTest_bound b hb (v n - w)))).1
  rw [map_sub, map_sub, hw, RCLike.ofReal_re] at ht
  have he := herr n
  have hn := scalar_ellOne_norm_tail (v n) (B n)
  change ‖v n - w‖ = ‖v n‖ - ∑ i ∈ B n, ‖v n i‖ at hn
  change ‖v n - w‖ < ε at he
  change ‖v n‖ - 2 * ε < RCLike.re (φ (v n))
  linarith

/-- Weakly null scalar ell-one sequences converge in norm. -/
theorem scalar_ellOne_schur (u : ℕ → lp (fun _ : I => 𝕜) 1)
    (hu : ∀ φ : lp (fun _ : I => 𝕜) 1 →L[𝕜] 𝕜,
      Tendsto (fun n => φ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
  suffices h : Tendsto u atTop (𝓝 0) by simpa only [norm_zero] using h.norm
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  suffices h : ∀ᶠ n in atTop, ‖u n‖ < ε by
    simpa only [dist_zero_right] using eventually_atTop.mp h
  by_contra h
  have hfreq : ∃ᶠ n in atTop, ε ≤ ‖u n‖ := by
    simpa only [not_lt] using Filter.not_eventually.mp h
  obtain ⟨s, hs, hsbound⟩ := extraction_of_frequently_atTop hfreq
  have hcoord (i : I) : Tendsto (fun n => u (s n) i) atTop (𝓝 0) :=
    (hu (lpCoordinate 1 i)).comp hs.tendsto_atTop
  obtain ⟨r, hr, φ, hφ⟩ := scalar_ellOne_subsequence_norm_test (fun n => u (s n))
    hcoord (show 0 < ε / 4 by linarith)
  have ht : Tendsto (fun n => RCLike.re (φ (u (s (r n))))) atTop (𝓝 0) := by
    simpa only [RCLike.zero_re] using
      ((RCLike.continuous_re.tendsto 0).comp
        (((hu φ).comp hs.tendsto_atTop).comp hr.tendsto_atTop))
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  have hb := hsbound (r n)
  have hp := hφ n
  linarith

theorem scalar_ellOne_schur_tendsto (u : ℕ → lp (fun _ : I => 𝕜) 1)
    (hu : ∀ φ : lp (fun _ : I => 𝕜) 1 →L[𝕜] 𝕜,
      Tendsto (fun n => φ (u n)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (scalar_ellOne_schur u hu)

theorem scalar_schur_of_equiv_ellOne {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (d : E ≃L[𝕜] lp (fun _ : I => 𝕜) 1) (u : ℕ → E)
    (hu : ∀ φ : E →L[𝕜] 𝕜, Tendsto (fun n => φ (u n)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  have ht := scalar_ellOne_schur_tendsto (fun n => d (u n))
    (fun φ => hu (φ.comp d.toContinuousLinearMap))
  have h := (d.symm.continuous.tendsto 0).comp ht
  simpa only [Function.comp_def, d.symm_apply_apply, map_zero] using h

end ThesisCommon
