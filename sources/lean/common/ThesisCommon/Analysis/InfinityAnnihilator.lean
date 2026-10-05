import ThesisCommon.Analysis.InfinityMask
import ThesisCommon.Analysis.AlmostDisjointFamily
import ThesisCommon.Analysis.DisjointSequenceBlocks

/-! Countably many ell_infinity functionals annihilating the unit vectors
vanish together on all vectors supported by a suitable infinite set. The
proof is the manuscript's almost-disjoint-family argument: each positive
threshold has only finitely many bad sets, and countably many thresholds
cannot exhaust a continuum-sized family.
-/
noncomputable section
open scoped Classical BigOperators ENNReal Cardinal
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

def infinityBadSets (S : Set (Set ℕ)) (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜) (ε : ℝ) :
    Set (Set ℕ) :=
  {A ∈ S | ∃ x : lp (fun _ : ℕ => 𝕜) ∞,
    (∀ n ∉ A, x n = 0) ∧ ‖x‖ ≤ 1 ∧ ε < ‖φ x‖}

theorem infinityBadSets_finite (S : Set (Set ℕ))
    (hS : S.Pairwise (fun A B => (A ∩ B).Finite))
    (φ : lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜)
    (hφ : ∀ n, φ (lp.single ∞ n (1 : 𝕜)) = 0) {ε : ℝ} (hε : 0 < ε) :
    (infinityBadSets S φ ε).Finite := by
  classical
  by_contra hinf
  have hinf' : (infinityBadSets S φ ε).Infinite := hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (‖φ‖ / ε)
  have hlarge : ‖φ‖ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  let a : Fin N ↪ Set ℕ := (Fin.valEmbedding.trans (hinf'.natEmbedding _)).trans
    (Function.Embedding.subtype _)
  have ha (i : Fin N) : a i ∈ infinityBadSets S φ ε := (hinf'.natEmbedding _ i).property
  choose x hx hn hxφ using fun i => (ha i).2
  let overlap : Set ℕ := ⋃ i : Fin N, ⋃ j : Fin N, if i = j then ∅ else a i ∩ a j
  have ho : overlap.Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.finite_iUnion
    intro j
    by_cases hij : i = j
    · simp only [if_pos hij]; exact Set.finite_empty
    · simp only [if_neg hij]
      exact hS (ha i).1 (ha j).1 (a.injective.ne hij)
  let F := ho.toFinset
  let y := fun i => infinityMask (F : Set ℕ)ᶜ (x i)
  have hy (i : Fin N) : ‖y i‖ ≤ 1 := (norm_infinityMask_apply_le _ _).trans (hn i)
  have hyφ (i : Fin N) : φ (y i) = φ (x i) := infinity_functional_remove_finite φ hφ F (x i)
  have hdis (i j : Fin N) (hij : i ≠ j) (n : ℕ) : y i n = 0 ∨ y j n = 0 := by
    by_cases hi : y i n = 0
    · exact Or.inl hi
    right
    by_contra hj
    have hnotF : n ∉ F := by
      intro hnF
      exact hi (by simp [y, hnF])
    have hmem (k : Fin N) (hk : y k n ≠ 0) : n ∈ a k := by
      by_contra hnk
      exact hk (by simp [y, hx k n hnk])
    apply hnotF
    apply ho.mem_toFinset.mpr
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
    simp only [if_neg hij]
    exact ⟨hmem i hi, hmem j hj⟩
  choose c hc hphase using fun i => RCLike.exists_norm_eq_mul_self (φ (y i))
  let z := fun i => c i • y i
  have hz (i : Fin N) : ‖z i‖ ≤ 1 := by simpa only [z, norm_smul, hc i, one_mul] using hy i
  have hzd (i j : Fin N) (hij : i ≠ j) (n : ℕ) : z i n = 0 ∨ z j n = 0 := by
    rcases hdis i j hij n with h | h
    · left; change c i * y i n = 0; rw [h, mul_zero]
    · right; change c j * y j n = 0; rw [h, mul_zero]
  have hsum : ‖∑ i : Fin N, z i‖ ≤ 1 := by
    simpa only [if_true] using infinity_norm_sign_sum_le z hz hzd (fun _ => true)
  have heq : φ (∑ i : Fin N, z i) = ((∑ i : Fin N, ‖φ (y i)‖ : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_sum]
    simp only [map_sum, z, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => (hphase i).symm)
  have hupper : (∑ i : Fin N, ‖φ (y i)‖) ≤ ‖φ‖ := by
    have hh := (φ.le_opNorm (∑ i : Fin N, z i)).trans
      ((mul_le_mul_of_nonneg_left hsum (norm_nonneg _)).trans_eq (mul_one _))
    rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hh
    exact hh
  have hlower : (N : ℝ) * ε ≤ ∑ i : Fin N, ‖φ (y i)‖ := by
    calc
      _ = ∑ _i : Fin N, ε := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by rw [hyφ]; exact (hxφ i).le)
  exact (not_le_of_gt hlarge) (hlower.trans hupper)

/-- An infinite common coordinate support for countably many residuals. -/
theorem infinity_common_annihilator
    (φ : ℕ → lp (fun _ : ℕ => 𝕜) ∞ →L[𝕜] 𝕜)
    (hφ : ∀ m n, φ m (lp.single ∞ n (1 : 𝕜)) = 0)
    {A : Set ℕ} (hA : A.Infinite) :
    ∃ M : Set ℕ, M ⊆ A ∧ M.Infinite ∧
      ∀ m (x : lp (fun _ : ℕ => 𝕜) ∞), (∀ n ∉ M, x n = 0) → φ m x = 0 := by
  classical
  obtain ⟨S, hcard, hsub, hAD⟩ := continuum_almostDisjoint_subsets A hA
  let bad : Set (Set ℕ) := ⋃ m : ℕ, ⋃ r : ℕ, infinityBadSets S (φ m) (1 / (r + 1 : ℝ))
  have hbad : bad.Countable := Set.countable_iUnion (fun m => Set.countable_iUnion (fun r =>
    (infinityBadSets_finite S hAD (φ m) (hφ m) (by positivity : 0 < 1 / (r + 1 : ℝ))).countable))
  have hnot : ¬ S ⊆ bad := by
    intro h
    have hh := Cardinal.le_aleph0_iff_set_countable.mpr (hbad.mono h)
    rw [hcard] at hh
    exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hh
  obtain ⟨M, hMS, hMbad⟩ := Set.not_subset.mp hnot
  have hunit (m : ℕ) (x : lp (fun _ : ℕ => 𝕜) ∞)
      (hx : ∀ n ∉ M, x n = 0) (hn : ‖x‖ ≤ 1) : φ m x = 0 := by
    by_contra hh
    obtain ⟨r, hr⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hh)
    apply hMbad
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨r, hMS, x, hx, hn, hr⟩⟩
  refine ⟨M, (hsub M hMS).1, (hsub M hMS).2, ?_⟩
  intro m x hx
  by_cases hzero : x = 0
  · simp [hzero]
  let y := (‖x‖⁻¹ : 𝕜) • x
  have hy : ‖y‖ ≤ 1 := (norm_smul_inv_norm (𝕜 := 𝕜) hzero).le
  have hys : ∀ n ∉ M, y n = 0 := by intro n hn; change (‖x‖⁻¹ : 𝕜) * x n = 0; rw [hx n hn, mul_zero]
  have hh := hunit m y hys hy
  change φ m ((‖x‖⁻¹ : 𝕜) • x) = 0 at hh
  rw [map_smul, smul_eq_mul] at hh
  apply (mul_eq_zero.mp hh).resolve_left
  exact inv_ne_zero ((RCLike.ofReal_ne_zero (K := 𝕜)).mpr (norm_ne_zero_iff.mpr hzero))

end ThesisCommon
