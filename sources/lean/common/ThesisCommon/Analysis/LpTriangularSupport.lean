import ThesisCommon.Analysis.CoordinateMaskSubspaces

/-! Support propagation and projection algebra on actual lp coordinate
subspaces. These lemmas prove invariance from single-coordinate data and
idempotence from the two explicit triangular invariance assertions. -/
noncomputable section
open Filter Topology
open scoped BigOperators ENNReal
namespace ThesisCommon
attribute [local instance] Classical.decEq
variable {𝕜 Γ X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem lp_operator_supported_of_single (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (A B : Set Γ)
    (hAB : ∀ α ∈ A, ∀ x : X, ∀ β ∉ B, T (lp.single p α x) β = 0)
    (x : lp (fun _ : Γ => X) p) (hx : ∀ α ∉ A, x α = 0) :
    ∀ β ∉ B, T x β = 0 := by
  classical
  intro β hβ
  let R : lp (fun _ : Γ => X) p →L[𝕜] X := (lpCoordinate p β).comp T
  have hz (α : Γ) : R (lp.single p α (x α)) = 0 := by
    by_cases hα : α ∈ A
    · exact hAB α hα (x α) β hβ
    · simp only [hx α hα, lp.single_zero, map_zero]
  have ht := (R.continuous.tendsto x).comp (lp.hasSum_single hp x)
  have hs : Tendsto (fun S : Finset Γ => R (∑ α ∈ S, lp.single p α (x α)))
      atTop (𝓝 0) := by
    simpa only [map_sum, hz, Finset.sum_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset Γ => (0 : X)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hs

theorem lpBlockCompression_idempotent_of_triangular (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (P : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (hP : P.comp P = P) (A D : Set Γ) (hAD : Disjoint A D)
    (hA : ∀ x : lp (fun _ : Γ => X) p, (∀ γ ∉ A, x γ = 0) →
      ∀ γ ∉ A ∪ D, P x γ = 0)
    (hD : ∀ x : lp (fun _ : Γ => X) p, (∀ γ ∉ D, x γ = 0) →
      ∀ γ ∉ D, P x γ = 0) :
    (lpBlockCompression p P A).comp (lpBlockCompression p P A) = lpBlockCompression p P A := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  let v : lp (fun _ : Γ => X) p := lpCoordinateProjection (𝕜 := 𝕜) p A (P x.val)
  let u : lp (fun _ : Γ => X) p := P x.val - v
  have hu : ∀ γ ∉ D, u γ = 0 := by
    intro γ hγD
    change P x.val γ - lpCoordinateProjection p A (P x.val) γ = 0
    by_cases hγA : γ ∈ A
    · simp only [lpCoordinateProjection_apply, if_pos hγA, sub_self]
    · rw [lpCoordinateProjection_apply, if_neg hγA, sub_zero]
      exact hA x.val x.property γ (fun h => h.elim hγA hγD)
  have hPu := hD u hu
  have hPv : P v = P x.val - P u := by
    have huv : v = P x.val - u := by dsimp only [u]; abel
    rw [huv, map_sub]
    have hPP := DFunLike.congr_fun hP x.val
    change P (P x.val) = P x.val at hPP
    rw [hPP]
  change lpCoordinateProjection p A (P v) = v
  apply lp.ext
  funext γ
  change lpCoordinateProjection p A (P v) γ = lpCoordinateProjection p A (P x.val) γ
  by_cases hγA : γ ∈ A
  · simp only [lpCoordinateProjection_apply, if_pos hγA]
    rw [hPv]
    change P x.val γ - P u γ = P x.val γ
    rw [hPu γ (fun hγD => Set.disjoint_left.mp hAD hγA hγD), sub_zero]
  · simp only [lpCoordinateProjection_apply, if_neg hγA]

/-- Only countably many disjoint coordinate blocks can meet a countable
operator support. This controls actual nonzero restricted block entries. -/
theorem countable_lp_block_entries {ι : Type*}
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : lp (fun _ : Γ => X) p →L[𝕜] lp (fun _ : Γ => X) p)
    (A : Set Γ) (B : ι → Set Γ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (S : Set Γ) (hS : S.Countable)
    (hT : ∀ x : lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A,
      ∀ γ ∉ S, T x γ = 0) :
    {i | ((lpCoordinateProjection (𝕜 := 𝕜) p (B i)).comp T).comp
      (lpSupportedSubmodule (𝕜 := 𝕜) (X := X) p A).subtypeL ≠ 0}.Countable := by
  classical
  have hhits : {i | (S ∩ B i).Nonempty}.Countable := by
    let J : Set ι := {i | (S ∩ B i).Nonempty}
    let f : J → S := fun i => ⟨i.property.choose, i.property.choose_spec.1⟩
    have hf (i : J) : (f i).val ∈ B i.val := i.property.choose_spec.2
    have hinj : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      by_contra hne
      apply Set.disjoint_left.mp (hB hne) (hf i)
      rw [show (f i).val = (f j).val from congrArg Subtype.val hij]
      exact hf j
    letI : Countable S := hS.to_subtype
    exact hinj.countable
  apply hhits.mono
  intro i hi
  by_contra hn
  apply hi
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext γ
  change lpCoordinateProjection p (B i) (T x) γ = 0
  by_cases hγ : γ ∈ B i
  · rw [lpCoordinateProjection_apply, if_pos hγ]
    exact hT x γ (fun hγS => hn ⟨γ, hγS, hγ⟩)
  · simp only [lpCoordinateProjection_apply, if_neg hγ]

end ThesisCommon
