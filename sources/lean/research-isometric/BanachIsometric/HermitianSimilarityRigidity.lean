import BanachIsometric.HermitianDeletionHyperplanes
import BanachIsometric.HermitianSimilarityNormalization

/-!
# Rigidity of actual simultaneous Hermitian similarities

Alternative to eigenvalue-multiset matching: deletion hyperplanes retaining
a common maximal eigenvector have scaling one by Rayleigh bounds. Trace then
identifies the deleted eigenvalues. A final deletion identifies the maximum.
The spectral basis and the normalized maps are constructed internally.
-/

namespace BanachIsometric

open scoped BigOperators ComplexConjugate

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
private theorem common_max_similarity_scale_one
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (H J : Submodule 𝕜 E)
    (U : H ≃ₗᵢ[𝕜] J) {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hscale : ∀ x : H, RCLike.re (B (U x : E) (U x : E)) =
      c * RCLike.re (B (x : E) (x : E)))
    (hbound : ∀ x : E, RCLike.re (B x x) ≤ M * ‖x‖ ^ 2)
    (x : H) (hx : ‖x‖ = 1) (hvalx : RCLike.re (B x.val x.val) = M)
    (y : J) (hy : ‖y‖ = 1) (hvaly : RCLike.re (B y.val y.val) = M) : c = 1 := by
  have hle : c * M ≤ M := by
    have hb := hbound (U x)
    rw [hscale, hvalx] at hb
    have hn : ‖(U x : E)‖ = 1 := by
      change ‖U x‖ = 1
      rw [U.norm_map, hx]
    rwa [hn, one_pow, mul_one] at hb
  have hge : M ≤ c * M := by
    have hb := hbound (U.symm y)
    have hn : ‖(U.symm y : E)‖ = 1 := by
      change ‖U.symm y‖ = 1
      rw [U.symm.norm_map, hy]
    rw [hn, one_pow, mul_one] at hb
    have hs := hscale (U.symm y)
    rw [U.apply_symm_apply, hvaly] at hs
    calc
      M = c * RCLike.re (B (U.symm y : E) (U.symm y : E)) := hs
      _ ≤ c * M := mul_le_mul_of_nonneg_left hb hc.le
  nlinarith

private theorem positive_spectral_deletions_rigid
    {n : ℕ} (hn : 2 ≤ n)
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (b : OrthonormalBasis (Fin (n + 1)) 𝕜 E) (a : Fin (n + 1) → ℝ)
    (hpos : ∀ i, 0 < a i)
    (heig : ∀ i, hermitianRelativeOperator B (b i) = (a i : 𝕜) • b i)
    (hsim : ∀ i j, ∃ U : orthonormalDeletionSubmodule b i ≃ₗᵢ[𝕜]
      orthonormalDeletionSubmodule b j, ∃ c : ℝ, 0 < c ∧
      ∀ x, RCLike.re (B (U x : E) (U x : E)) = c * RCLike.re (B (x : E) (x : E))) :
    ∀ i j, a i = a j := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ a
    (show (Finset.univ : Finset (Fin (n + 1))).Nonempty from ⟨0, Finset.mem_univ 0⟩)
  have hmax (k : Fin (n + 1)) : a k ≤ a m := hm k (Finset.mem_univ k)
  have hbound (x : E) : RCLike.re (B x x) ≤ a m * ‖x‖ ^ 2 := by
    rw [← inner_hermitianRelativeOperator B hB]
    exact re_inner_apply_le_eigenvalue_bound _ (hermitianRelativeOperator_isSymmetric B hB)
      b a heig hmax x
  let v (i k : Fin (n + 1)) (hki : k ≠ i) : orthonormalDeletionSubmodule b i :=
    orthonormalDeletionBasis b i ⟨k, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩⟩
  have hv (i k : Fin (n + 1)) (hki : k ≠ i) : (v i k hki : E) = b k :=
    orthonormalDeletionBasis_apply b i _
  have hvnorm (i k : Fin (n + 1)) (hki : k ≠ i) : ‖v i k hki‖ = 1 :=
    (orthonormalDeletionBasis b i).orthonormal.1 _
  have hvval (i k : Fin (n + 1)) (hki : k ≠ i) :
      RCLike.re (B (v i k hki : E) (v i k hki : E)) = a k := by
    rw [hv i k hki]
    exact re_relativeOperator_eigenvector_diagonal B hB _ (b.orthonormal.1 k) _ (heig k)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp
    (show 2 < Fintype.card (Fin (n + 1)) by simp only [Fintype.card_fin]; omega)
  have htwo : ∃ i j : Fin (n + 1), i ≠ m ∧ j ≠ m ∧ i ≠ j := by
    by_cases hrm : r = m
    · subst r
      exact ⟨s, t, hrs.symm, hrt.symm, hst⟩
    by_cases hsm : s = m
    · subst s
      exact ⟨r, t, hrs, hst.symm, hrt⟩
    exact ⟨r, s, hrm, hsm, hrs⟩
  obtain ⟨i, j, him, hjm, hij⟩ := htwo
  have hsame (k : Fin (n + 1)) (hkm : k ≠ m) : a k = a i := by
    obtain ⟨U, c, hc, hs⟩ := hsim k i
    have hc1 : c = 1 := common_max_similarity_scale_one B _ _ U hc (hpos m) hs hbound
      (v k m hkm.symm) (hvnorm k m hkm.symm) (hvval k m hkm.symm)
      (v i m him.symm) (hvnorm i m him.symm) (hvval i m him.symm)
    have htrace := re_trace_relativeOperator_scaling_of_isometry
      (restrictSesqForm B (orthonormalDeletionSubmodule b k))
      (restrictSesqForm B (orthonormalDeletionSubmodule b i))
      (restrictSesqForm_hermitian B hB _) (restrictSesqForm_hermitian B hB _) U c hs
    rw [re_trace_orthonormalDeletion B hB b a heig,
      re_trace_orthonormalDeletion B hB b a heig, hc1, one_mul] at htrace
    have hk := Finset.sum_erase_add Finset.univ a (Finset.mem_univ k)
    have hi := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
    linarith
  have hconstant (x : orthonormalDeletionSubmodule b m) :
      RCLike.re (B x.val x.val) = a i * ‖x‖ ^ 2 := by
    let D := restrictSesqForm B (orthonormalDeletionSubmodule b m)
    let bm := orthonormalDeletionBasis b m
    have hD := restrictSesqForm_hermitian B hB (orthonormalDeletionSubmodule b m)
    have hd (k : Finset.univ.erase m) :
        hermitianRelativeOperator D (bm k) = (a k.val : 𝕜) • bm k := by
      apply relativeOperator_restrict_eigenvector
      simpa only [bm, orthonormalDeletionBasis_apply] using heig k.val
    have h := re_inner_apply_eq_sum_eigenvalues (hermitianRelativeOperator D)
      (hermitianRelativeOperator_isSymmetric D hD) bm (fun k => a k.val) hd x
    rw [inner_hermitianRelativeOperator D hD] at h
    change RCLike.re (B x.val x.val) = _ at h
    rw [h]
    have hc (k : Finset.univ.erase m) : a k.val = a i :=
      hsame k.val (Finset.mem_erase.mp k.property).1
    simp_rw [hc]
    rw [← Finset.mul_sum, bm.sum_sq_norm_inner_right]
  obtain ⟨U, c, _, hs⟩ := hsim m i
  have hvalue (k : Fin (n + 1)) (hki : k ≠ i) : a k = c * a i := by
    have h := hs (U.symm (v i k hki))
    rw [U.apply_symm_apply, hvval i k hki, hconstant, U.symm.norm_map, hvnorm i k hki,
      one_pow, mul_one] at h
    exact h
  have hmi : a m = a i := by
    have hm' := hvalue m him.symm
    have hj' := hvalue j hij.symm
    rw [hsame j hjm] at hj'
    linarith
  have hall (k : Fin (n + 1)) : a k = a i := by
    by_cases hkm : k = m
    · simpa only [hkm] using hmi
    · exact hsame k hkm
  exact fun k l => (hall k).trans (hall l).symm

/-- Actual simultaneous scalar-linear similarities of the first norm and
second positive Hermitian square force proportional squares in dimension
`n+1`. The relative operator and its spectral basis are derived internally. -/
theorem hermitianSquare_proportional_of_simultaneous_similarities
    {n : ℕ} (hn : 2 ≤ n) (hdim : Module.finrank 𝕜 E = n + 1)
    (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (hB : ∀ x y, star (B x y) = B y x)
    (hpos : ∀ x : E, x ≠ 0 → 0 < RCLike.re (B x x))
    (hsim : ∀ H J : Submodule 𝕜 E, Module.finrank 𝕜 H = n → Module.finrank 𝕜 J = n →
      ∃ T : H ≃ₗ[𝕜] J, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        (∀ x, ‖T x‖ = c₁ * ‖x‖) ∧
        ∀ x, RCLike.re (B (T x : E) (T x : E)) = c₂ ^ 2 * RCLike.re (B (x : E) (x : E))) :
    ∃ A : ℝ, 0 < A ∧ ∀ x, RCLike.re (B x x) = A * ‖x‖ ^ 2 := by
  obtain ⟨b, a, ha, heig⟩ := exists_positive_eigenbasis_hermitianRelativeOperator B hB hpos hdim
  have hmaps (i j : Fin (n + 1)) := hsim
    (orthonormalDeletionSubmodule b i) (orthonormalDeletionSubmodule b j)
    (by rw [orthonormalDeletionSubmodule_finrank, Fintype.card_fin]; omega)
    (by rw [orthonormalDeletionSubmodule_finrank, Fintype.card_fin]; omega)
  have hnorm : ∀ i j, ∃ U : orthonormalDeletionSubmodule b i ≃ₗᵢ[𝕜]
      orthonormalDeletionSubmodule b j, ∃ c : ℝ, 0 < c ∧
      ∀ x, RCLike.re (B (U x : E) (U x : E)) = c * RCLike.re (B (x : E) (x : E)) := by
    intro i j
    obtain ⟨T, c₁, c₂, hc₁, hc₂, hp, hq⟩ := hmaps i j
    exact exists_normalized_simultaneous_hermitian_similarity
      (restrictSesqForm B (orthonormalDeletionSubmodule b i))
      (restrictSesqForm B (orthonormalDeletionSubmodule b j)) T c₁ c₂ hc₁ hc₂ hp hq
  have hall := positive_spectral_deletions_rigid hn B hB b a ha heig hnorm
  refine ⟨a 0, ha 0, ?_⟩
  intro x
  rw [← inner_hermitianRelativeOperator B hB,
    re_inner_apply_eq_sum_eigenvalues _ (hermitianRelativeOperator_isSymmetric B hB) b a heig]
  simp_rw [hall _ 0]
  rw [← Finset.mul_sum, b.sum_sq_norm_inner_right]

end

end BanachIsometric
