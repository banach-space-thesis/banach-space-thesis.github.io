import Sigma.ComplexLocalizedWitness
import Sigma.ComplexMeasureSeparation

/-! Complex simultaneous preservation under arbitrary changes inside a chosen support.
The scalar-independent local-witness type and cardinal estimates are reused. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem complex_bad_localized_cardinal_le (B Btilde : BooleanSubalgebra (Set ℕ))
    (hfinite : ∀ F : Set ℕ, F.Finite → F ∈ B)
    (M N : Set ComplexPairedMeasure) (hnsep : ¬ ComplexPairedSeparated B Btilde M N)
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hB : #B ≤ κ) (hBtilde : #Btilde ≤ κ) :
    #{Z : Set ℕ // Z ∈ S ∧ ComplexPairedSeparated (localizedAlgebra B Z) Btilde M N} ≤ κ := by
  let successes : LocalSeparationWitness B Btilde → Set (Set ℕ) :=
    fun w => {Z | Z ∈ S ∧ w.ComplexSeparates Z M N}
  have hf (w : LocalSeparationWitness B Btilde) : #(successes w) ≤ κ := by
    haveI : Finite (successes w) := w.complex_finite_successes hfinite M N hnsep S hS
    exact Cardinal.mk_le_aleph0.trans hκ
  have hcover : {Z | Z ∈ S ∧ ComplexPairedSeparated (localizedAlgebra B Z) Btilde M N} ⊆
      ⋃ w, successes w := by
    rintro Z ⟨hZS, hsep⟩
    obtain ⟨w, hw⟩ := complex_localSeparationWitness_exists B Btilde Z M N hsep
    exact Set.mem_iUnion.mpr ⟨w, hZS, hw⟩
  calc
    _ ≤ #(⋃ w, successes w) := Cardinal.mk_le_mk_of_subset hcover
    _ ≤ #(LocalSeparationWitness B Btilde) * ⨆ w, #(successes w) := Cardinal.mk_iUnion_le successes
    _ ≤ κ * κ := mul_le_mul' (localSeparationWitness_cardinal_le B Btilde κ hκ hB hBtilde)
      (ciSup_le' hf)
    _ = κ := Cardinal.mul_eq_self hκ

/-- Strengthening of Proposition 4.4 for all subsets of the chosen support. All stages are
handled simultaneously; no regularity of the continuum is assumed. -/
theorem complex_localized_haydon_selection {I : Type} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ B i)
    (M N : I → Set ComplexPairedMeasure) (hnsep : ∀ i, ¬ ComplexPairedSeparated (B i) (Btilde i) (M i) (N i))
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite)) (hcard : #S = 𝔠) :
    ∃ Z ∈ S, ∀ i, ¬ ComplexPairedSeparated (localizedAlgebra (B i) Z) (Btilde i) (M i) (N i) := by
  let bad : I → Set (Set ℕ) := fun i =>
    {Z | Z ∈ S ∧ ComplexPairedSeparated (localizedAlgebra (B i) Z) (Btilde i) (M i) (N i)}
  have hbad (i : I) : #(bad i) ≤ κ :=
    complex_bad_localized_cardinal_le (B i) (Btilde i) (hfinite i) (M i) (N i) (hnsep i)
      S hS κ hκ (hB i) (hBtilde i)
  have hbadall : #(⋃ i, bad i) < 𝔠 := by
    calc
      _ ≤ #I * ⨆ i, #(bad i) := Cardinal.mk_iUnion_le bad
      _ ≤ κ * κ := mul_le_mul' hI (ciSup_le' hbad)
      _ = κ := Cardinal.mul_eq_self hκ
      _ < 𝔠 := hκlt
  have hnot : ¬ S ⊆ ⋃ i, bad i := by
    intro h
    have hle := Cardinal.mk_le_mk_of_subset h
    rw [hcard] at hle
    exact (not_le_of_gt hbadall) hle
  obtain ⟨Z, hZS, hZ⟩ := Set.not_subset.mp hnot
  refine ⟨Z, hZS, ?_⟩
  intro i hsep
  exact hZ (Set.mem_iUnion.mpr ⟨i, hZS, hsep⟩)

/-- The corresponding local-extension result on the second base. -/
theorem complex_localized_haydon_selection_right {I : Type} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hκlt : κ < 𝔠) (hI : #I ≤ κ)
    (hB : ∀ i, #(B i) ≤ κ) (hBtilde : ∀ i, #(Btilde i) ≤ κ)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ Btilde i)
    (M N : I → Set ComplexPairedMeasure) (hnsep : ∀ i, ¬ ComplexPairedSeparated (B i) (Btilde i) (M i) (N i))
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite)) (hcard : #S = 𝔠) :
    ∃ Z ∈ S, ∀ i, ¬ ComplexPairedSeparated (B i) (localizedAlgebra (Btilde i) Z) (M i) (N i) := by
  have hnsep' (i : I) :
      ¬ ComplexPairedSeparated (Btilde i) (B i) (complexSwapMeasure '' M i) (complexSwapMeasure '' N i) :=
    fun h => hnsep i ((complexPairedSeparated_swap_iff (B i) (Btilde i) (M i) (N i)).mp h)
  obtain ⟨Z, hZS, hZ⟩ := complex_localized_haydon_selection Btilde B κ hκ hκlt hI hBtilde hB hfinite
    (fun i => complexSwapMeasure '' M i) (fun i => complexSwapMeasure '' N i) hnsep' S hS hcard
  exact ⟨Z, hZS, fun i h => hZ i (complexPairedSeparated_swap (B i) (localizedAlgebra (Btilde i) Z)
    (M i) (N i) h)⟩

end SigmaNonprimarity
