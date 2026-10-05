import ThesisCommon.Analysis.WCGEllOneSupport

/-! The outgoing support needed when the countable model is ℓ1(ℕ,X).
The WCG hypothesis is used on each genuine X-coordinate, then a countable
union and the source's actual finite-sum expansion control the whole model. -/
noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem IsWeaklyCompactlyGenerated.ellOne_operator_countable_support_to
    (hX : IsWeaklyCompactlyGenerated 𝕜 X) (T : X →L[𝕜] lp (fun _ : Γ => Y) 1) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : X, ∀ γ ∉ Λ, T x γ = 0 := by
  classical
  have hw : ∀ γ, ∃ x : X, (∃ y : X, T y γ ≠ 0) → T x γ ≠ 0 := by
    intro γ
    by_cases h : ∃ y : X, T y γ ≠ 0
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose x hx using hw
  choose φ hφ hφx using fun γ => exists_dual_vector'' 𝕜 (T (x γ) γ)
  let S : X →L[𝕜] lp (fun _ : Γ => 𝕜) 1 :=
    (lpDiagonal 1 φ 1 zero_le_one hφ).comp T
  obtain ⟨Λ, hΛ, hsupp⟩ := lp_separable_countable_support (𝕜 := 𝕜)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hX.ellOne_operator_separable_range S)
  refine ⟨Λ, hΛ, ?_⟩
  intro y γ hγ
  by_contra hy
  have hn : T (x γ) γ ≠ 0 := hx γ ⟨y, hy⟩
  have hz : S (x γ) γ = 0 := by
    by_contra hne
    exact hγ (hsupp (S (x γ)) ⟨x γ, rfl⟩ hne)
  simp only [S, ContinuousLinearMap.comp_apply, lpDiagonal_apply, hφx] at hz
  exact (norm_ne_zero_iff.mpr hn) (RCLike.ofReal_eq_zero.mp hz)

theorem IsWeaklyCompactlyGenerated.iterated_ellOne_operator_countable_support
    (hX : IsWeaklyCompactlyGenerated 𝕜 X)
    (T : lp (fun _ : ℕ => X) 1 →L[𝕜] lp (fun _ : Γ => Y) 1) :
    ∃ Λ : Set Γ, Λ.Countable ∧ ∀ x : lp (fun _ : ℕ => X) 1, ∀ γ ∉ Λ, T x γ = 0 := by
  classical
  have hn (n : ℕ) := hX.ellOne_operator_countable_support_to
    (T.comp (lp.singleContinuousLinearMap (𝕜 := 𝕜) (p := 1) (E := fun _ : ℕ => X) n))
  choose A hA hTA using hn
  let Λ : Set Γ := ⋃ n, A n
  refine ⟨Λ, Set.countable_iUnion hA, ?_⟩
  intro x γ hγ
  let R : lp (fun _ : ℕ => X) 1 →L[𝕜] Y := (lpCoordinate 1 γ).comp T
  have hz (n : ℕ) : R (lp.single 1 n (x n)) = 0 := by
    exact hTA n (x n) γ (fun h => hγ (Set.mem_iUnion.mpr ⟨n, h⟩))
  have ht := (R.continuous.tendsto x).comp (lp.hasSum_single (by norm_num) x)
  have hs : Tendsto (fun F : Finset ℕ => R (∑ n ∈ F, lp.single 1 n (x n)))
      atTop (𝓝 0) := by
    simpa only [map_sum, hz, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset ℕ => (0 : Y)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hs

end ThesisCommon
