import ThesisCommon.Analysis.MatrixRamseySlices
import ThesisCommon.Analysis.BoundedScalarFiniteColoring

/-! Uniform finite matrix coefficient scalarisation: the cutoff is chosen
before the ambient dimension and the operator. -/
noncomputable section
namespace ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem exists_matrix_coefficient_scalarisation (p : BanachExponent)
    (hp : 1 < p.val.toReal) (n : ℕ) {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : FiniteMatrixBlock 𝕜 p N →L[𝕜] FiniteMatrixBlock 𝕜 p N, ‖T‖ ≤ K →
      ∃ (α τ : Fin n ↪o Fin N) (c : 𝕜),
        Disjoint (Set.range α) (Set.range τ) ∧
        ∀ i j k l : Fin n,
          ‖matrixEntry p (α k) (τ l) (T (matrixUnit p (α i) (τ j))) -
            (if k = i ∧ l = j then c else 0)‖ ≤ δ := by
  classical
  obtain ⟨m, _, hcol, hrow⟩ := exists_matrix_row_column_power_cutoff p hp K hδ
  obtain ⟨D, hD, color, hcolor⟩ := exists_bounded_scalar_coloring (𝕜 := 𝕜) hK hδ
  letI : Nonempty D := hD.to_subtype
  let L := max (2 * n) (m + 3)
  obtain ⟨N₀, hN₀, hRamsey⟩ := finite_matrix_pattern_selection D m L (le_max_right _ _)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN T hT
  let f := matrixNatCoefficient p T
  let pairColor (e : Fin 2 ↪o ℕ) := color (f (e 0) (e 1) (e 0) (e 1))
  obtain ⟨S, hSN, hSL, ⟨c, hc⟩, h₃, h₄⟩ :=
    hRamsey (Finset.range N) (by simpa using hN) pairColor
      (fun i j k l => ‖f i j k l‖) δ
      (matrix_good_slices_of_power_bounds p hp T hT hcol hrow)
  let e := S.orderEmbOfFin hSL
  have heS (r : Fin L) : e r ∈ (S : Set ℕ) := S.orderEmbOfFin_mem hSL r
  have hnL : n ≤ L := by dsimp [L]; omega
  have h2nL : n + n ≤ L := by dsimp [L]; omega
  let a := orderedWindow e 0 (by omega : 0 + n ≤ L)
  let b := orderedWindow e n h2nL
  have haS (i : Fin n) : a i ∈ (S : Set ℕ) := heS _
  have hbS (i : Fin n) : b i ∈ (S : Set ℕ) := heS _
  have haN (i : Fin n) : a i < N := Finset.mem_range.mp (hSN (haS i))
  have hbN (i : Fin n) : b i < N := Finset.mem_range.mp (hSN (hbS i))
  let α : Fin n ↪o Fin N := OrderEmbedding.ofStrictMono
    (fun i => ⟨a i, haN i⟩) (fun i j hij => a.strictMono hij)
  let τ : Fin n ↪o Fin N := OrderEmbedding.ofStrictMono
    (fun i => ⟨b i, hbN i⟩) (fun i j hij => b.strictMono hij)
  have hab (i j : Fin n) : a i < b j := by
    apply e.strictMono
    change 0 + i.val < n + j.val
    omega
  refine ⟨α, τ, (c : 𝕜), ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    have hh : a i = b j := (congrArg Fin.val hj).symm
    exact (ne_of_lt (hab i j)) hh
  · intro i j k l
    by_cases hdiag : k = i ∧ l = j
    · rcases hdiag with ⟨rfl,rfl⟩
      simp only [and_self, if_true]
      have hh := hc (orderedPair (a k) (b l) (hab k l))
        (range_orderedPair_subset (hab k l) (haS k) (hbS l))
      have hh' : color (f (a k) (b l) (a k) (b l)) = c := by
        simpa [pairColor, orderedPair] using hh
      have hz := hcolor (f (a k) (b l) (a k) (b l))
        ((matrixNatCoefficient_norm_le p T _ _ _ _).trans hT)
      rw [hh'] at hz
      simpa only [f, ← matrixNatCoefficient_fin p T (α k) (τ l) (α k) (τ l)] using hz
    · rw [if_neg hdiag, sub_zero]
      have hne : a i ≠ a k ∨ b j ≠ b l := by
        by_contra! h
        exact hdiag ⟨(a.injective h.1).symm, (b.injective h.2).symm⟩
      have hh := matrix_patterns_small h₃ h₄ (haS i) (hbS j) (haS k) (hbS l)
        (hab i j) (hab i l) (hab k j) (hab k l) hne
      have hh' : ‖matrixEntry p (α k) (τ l) (T (matrixUnit p (α i) (τ j)))‖ < δ := by
        simpa only [f, ← matrixNatCoefficient_fin p T (α i) (τ j) (α k) (τ l)] using hh
      exact hh'.le

end ThesisCommon

