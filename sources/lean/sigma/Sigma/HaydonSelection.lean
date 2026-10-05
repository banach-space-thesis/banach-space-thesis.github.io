import Sigma.HaydonWitness
import Sigma.PairedMeasureSwap

/-! Haydon's counting argument for simultaneously preserving nonseparation. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

theorem bad_generators_cardinal_le (B Btilde : BooleanSubalgebra (Set ℕ))
    (hfinite : ∀ F : Set ℕ, F.Finite → F ∈ B)
    (M N : Set PairedMeasure) (hnsep : ¬ PairedSeparated B Btilde M N)
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite))
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) (hB : #B ≤ κ) (hBtilde : #Btilde ≤ κ) :
    #{Z : Set ℕ // Z ∈ S ∧ PairedSeparated (adjoinSet B Z) Btilde M N} ≤ κ := by
  let successes : SeparationWitness B Btilde → Set (Set ℕ) :=
    fun w => {Z | Z ∈ S ∧ w.Separates Z M N}
  have hf (w : SeparationWitness B Btilde) : #(successes w) ≤ κ := by
    haveI : Finite (successes w) := w.finite_successes hfinite M N hnsep S hS
    exact Cardinal.mk_le_aleph0.trans hκ
  have hcover : {Z | Z ∈ S ∧ PairedSeparated (adjoinSet B Z) Btilde M N} ⊆
      ⋃ w, successes w := by
    rintro Z ⟨hZS, hsep⟩
    obtain ⟨w, hw⟩ := separationWitness_exists B Btilde Z M N hsep
    exact Set.mem_iUnion.mpr ⟨w, hZS, hw⟩
  calc
    _ ≤ #(⋃ w, successes w) := Cardinal.mk_le_mk_of_subset hcover
    _ ≤ #(SeparationWitness B Btilde) * ⨆ w, #(successes w) := Cardinal.mk_iUnion_le successes
    _ ≤ κ * κ := mul_le_mul' (separationWitness_cardinal_le B Btilde κ hκ hB hBtilde)
      (ciSup_le' hf)
    _ = κ := Cardinal.mul_eq_self hκ

/-- Proposition 4.4 for adjoining a set on the first base. All stages are
handled simultaneously; no regularity of the continuum is assumed. -/
theorem haydon_selection {I : Type} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hI : #I < 𝔠)
    (hB : ∀ i, #(B i) ≤ #I) (hBtilde : ∀ i, #(Btilde i) ≤ #I)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ B i)
    (M N : I → Set PairedMeasure) (hnsep : ∀ i, ¬ PairedSeparated (B i) (Btilde i) (M i) (N i))
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite)) (hcard : #S = 𝔠) :
    ∃ Z ∈ S, ∀ i, ¬ PairedSeparated (adjoinSet (B i) Z) (Btilde i) (M i) (N i) := by
  let κ : Cardinal := max #I ℵ₀
  have hκ : ℵ₀ ≤ κ := le_max_right _ _
  have hκlt : κ < 𝔠 := max_lt hI Cardinal.aleph0_lt_continuum
  let bad : I → Set (Set ℕ) := fun i =>
    {Z | Z ∈ S ∧ PairedSeparated (adjoinSet (B i) Z) (Btilde i) (M i) (N i)}
  have hbad (i : I) : #(bad i) ≤ κ :=
    bad_generators_cardinal_le (B i) (Btilde i) (hfinite i) (M i) (N i) (hnsep i)
      S hS κ hκ ((hB i).trans (le_max_left _ _)) ((hBtilde i).trans (le_max_left _ _))
  have hbadall : #(⋃ i, bad i) < 𝔠 := by
    calc
      _ ≤ #I * ⨆ i, #(bad i) := Cardinal.mk_iUnion_le bad
      _ ≤ κ * κ := mul_le_mul' (le_max_left _ _) (ciSup_le' hbad)
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

/-- The corresponding half of Proposition 4.4 for the second base. -/
theorem haydon_selection_right {I : Type} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hI : #I < 𝔠)
    (hB : ∀ i, #(B i) ≤ #I) (hBtilde : ∀ i, #(Btilde i) ≤ #I)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ Btilde i)
    (M N : I → Set PairedMeasure) (hnsep : ∀ i, ¬ PairedSeparated (B i) (Btilde i) (M i) (N i))
    (S : Set (Set ℕ)) (hS : S.Pairwise (fun Z W => (Z ∩ W).Finite)) (hcard : #S = 𝔠) :
    ∃ Z ∈ S, ∀ i, ¬ PairedSeparated (B i) (adjoinSet (Btilde i) Z) (M i) (N i) := by
  have hnsep' (i : I) :
      ¬ PairedSeparated (Btilde i) (B i) (swapMeasure '' M i) (swapMeasure '' N i) :=
    fun h => hnsep i ((pairedSeparated_swap_iff (B i) (Btilde i) (M i) (N i)).mp h)
  obtain ⟨Z, hZS, hZ⟩ := haydon_selection Btilde B hI hBtilde hB hfinite
    (fun i => swapMeasure '' M i) (fun i => swapMeasure '' N i) hnsep' S hS hcard
  exact ⟨Z, hZS, fun i h => hZ i (pairedSeparated_swap (B i) (adjoinSet (Btilde i) Z)
    (M i) (N i) h)⟩

end SigmaNonprimarity
