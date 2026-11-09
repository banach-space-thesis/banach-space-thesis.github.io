import Sigma.HaydonSelection
import Sigma.PointCoding
import Sigma.ThreeLevelSelection

/-! The numbered statements of Section 4 in the form in which they are printed.
The copies of the countable base are labelled by the two injections into
`ℕ ⊕ ℕ`. In Lemma 4.7 either copy of `ω × 2` is represented by `Point`. -/
noncomputable section
open Set Cardinal ThesisCommon
namespace SigmaNonprimarity

/-- A simple measurable function on a Boolean algebra: finite range, with
each nonempty fibre in the algebra. -/
def IsBooleanSimple (B : BooleanSubalgebra (Set ℕ)) (g : ℕ → ℝ) : Prop :=
  (range g).Finite ∧ ∀ r ∈ range g, g ⁻¹' {r} ∈ B

/-- Integration of a finite-range function against a finitely additive
measure on the two bases, using the indicated injection of its base. -/
def simpleChargeIntegral (μ : PairedMeasure) (tag : ℕ → ℕ ⊕ ℕ)
    (g : ℕ → ℝ) (hg : (range g).Finite) : ℝ :=
  letI := hg.fintype
  ∑ r : range g, r.val * μ (tag '' (g ⁻¹' {r.val}))

/-- Pairing with the sum of two simple functions on the disjoint bases. -/
def pairedSimpleIntegral (μ : PairedMeasure) (g gtilde : ℕ → ℝ)
    (hg : (range g).Finite) (hgt : (range gtilde).Finite) : ℝ :=
  simpleChargeIntegral μ Sum.inl g hg + simpleChargeIntegral μ Sum.inr gtilde hgt

/-- Lemma 4.2: a uniform gap on the sum of the two simple functions
implies separation by finitely many sets in the two algebras. -/
theorem lemma_4_2_printed (B Btilde : BooleanSubalgebra (Set ℕ))
    (M N : Set PairedMeasure) (g gtilde : ℕ → ℝ)
    (hg : IsBooleanSimple B g) (hgt : IsBooleanSimple Btilde gtilde)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ μ ∈ M, ∀ ν ∈ N,
      ε ≤ |pairedSimpleIntegral μ g gtilde hg.1 hgt.1 -
        pairedSimpleIntegral ν g gtilde hg.1 hgt.1|) :
    PairedSeparated B Btilde M N := by
  classical
  letI := hg.1.fintype
  letI := hgt.1.fintype
  let test : range g ⊕ range gtilde → B ⊕ Btilde :=
    Sum.map (fun r => ⟨g ⁻¹' {r.val}, hg.2 r.val r.property⟩)
      (fun r => ⟨gtilde ⁻¹' {r.val}, hgt.2 r.val r.property⟩)
  let c : range g ⊕ range gtilde → ℝ := Sum.elim Subtype.val Subtype.val
  let ev (μ : PairedMeasure) (t : range g ⊕ range gtilde) :=
    μ (pairedTest B Btilde (test t))
  have heval (μ : PairedMeasure) :
      (∑ t, c t * ev μ t) = pairedSimpleIntegral μ g gtilde hg.1 hgt.1 := by
    rw [Fintype.sum_sum_type]
    rfl
  have h : FinitelySeparated ev univ M N :=
    finitelySeparated_of_sum_gap ev univ M N Finset.univ (subset_univ _) c hε (by
      intro μ hμ ν hν
      rw [heval, heval]
      exact hgap μ hμ ν hν)
  obtain ⟨δ, hδ, F, _, hsep⟩ := h
  refine ⟨δ, hδ, F.image test, subset_univ _, ?_⟩
  intro μ hμ ν hν
  obtain ⟨t, ht, hbound⟩ := hsep μ hμ ν hν
  exact ⟨test t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hbound⟩

/-- Lemma 4.3 with the printed infinite-set hypothesis. The existing
counting theorem also applies to finite sets of measures. -/
theorem lemma_4_3_printed (B Btilde : BooleanSubalgebra (Set ℕ))
    (hB : #B < 𝔠) (hBtilde : #Btilde < 𝔠) (M : Set PairedMeasure) (_hM : M.Infinite) :
    #{A : Set PairedMeasure // A ⊆ M ∧ PairedSeparated B Btilde A (M \ A)} < 𝔠 :=
  separated_measure_cuts_lt_continuum B Btilde hB hBtilde M

/-- Proposition 4.4, for adjoining one set. The two clauses are the
printed first-base conclusion and its second-base counterpart. The cardinal
bound allows the index type to be relabelled in the universe of the bases. -/
theorem proposition_4_4_printed {I : Type u} (B Btilde : I → BooleanSubalgebra (Set ℕ))
    (hI : #I < Cardinal.lift.{u} (𝔠 : Cardinal.{0}))
    (hB : ∀ i, Cardinal.lift.{u} #(B i) ≤ #I)
    (hBtilde : ∀ i, Cardinal.lift.{u} #(Btilde i) ≤ #I)
    (hfinite : ∀ i (F : Set ℕ), F.Finite → F ∈ B i)
    (hfiniteTil : ∀ i (F : Set ℕ), F.Finite → F ∈ Btilde i)
    (M N : I → Set PairedMeasure)
    (hnsep : ∀ i, ¬ PairedSeparated (B i) (Btilde i) (M i) (N i)) :
    (∀ S : Set (Set ℕ), (∀ Z ∈ S, Z.Infinite) →
      S.Pairwise (fun Z W => (Z ∩ W).Finite) → #S = 𝔠 →
      ∃ Z ∈ S, ∀ i, ¬ PairedSeparated (adjoinSet (B i) Z) (Btilde i) (M i) (N i)) ∧
    (∀ S : Set (Set ℕ), (∀ Z ∈ S, Z.Infinite) →
      S.Pairwise (fun Z W => (Z ∩ W).Finite) → #S = 𝔠 →
      ∃ Z ∈ S, ∀ i, ¬ PairedSeparated (B i) (adjoinSet (Btilde i) Z) (M i) (N i)) := by
  obtain ⟨f⟩ : Nonempty (I ↪ Set ℕ) := Cardinal.lift_mk_le'.mp (by
    simpa only [Cardinal.lift_uzero, Cardinal.mk_set_nat] using hI.le)
  letI : Small.{0} I := small_of_injective f.injective
  let J := Shrink.{0} I
  let e : J ≃ I := (equivShrink I).symm
  have hsize : Cardinal.lift.{u} #J = #I := by
    simpa only [Cardinal.lift_uzero] using Cardinal.lift_mk_shrink'.{u, 0} I
  have hJ : #J < 𝔠 := Cardinal.lift_lt.mp (hsize.trans_lt hI)
  have hBJ (j : J) : #(B (e j)) ≤ #J :=
    Cardinal.lift_le.mp ((hB (e j)).trans_eq hsize.symm)
  have hBTJ (j : J) : #(Btilde (e j)) ≤ #J :=
    Cardinal.lift_le.mp ((hBtilde (e j)).trans_eq hsize.symm)
  constructor
  · intro S _ hS hcard
    obtain ⟨Z, hZS, hZ⟩ := haydon_selection (B ∘ e) (Btilde ∘ e) hJ hBJ hBTJ
      (fun j => hfinite (e j)) (M ∘ e) (N ∘ e) (fun j => hnsep (e j)) S hS hcard
    exact ⟨Z, hZS, fun i => by simpa only [Function.comp_apply, e.apply_symm_apply] using hZ (e.symm i)⟩
  · intro S _ hS hcard
    obtain ⟨Z, hZS, hZ⟩ := haydon_selection_right (B ∘ e) (Btilde ∘ e) hJ hBJ hBTJ
      (fun j => hfiniteTil (e j)) (M ∘ e) (N ∘ e) (fun j => hnsep (e j)) S hS hcard
    exact ⟨Z, hZS, fun i => by simpa only [Function.comp_apply, e.apply_symm_apply] using hZ (e.symm i)⟩

/-- Lemma 4.5 with the same old sets for every member of the almost
disjoint family and the printed strict bound on its size. -/
theorem lemma_4_5_printed (B Btilde : BooleanSubalgebra (Set ℕ))
    (hfinite : ∀ F : Set ℕ, F.Finite → F ∈ B)
    (_hfiniteTil : ∀ F : Set ℕ, F.Finite → F ∈ Btilde)
    (M N : Set PairedMeasure) {n m k : ℕ} (ε : ℝ) (hε : 0 < ε)
    (hk : 12 * (n : ℝ) / ε < (k : ℝ))
    (Z : Fin k → Set ℕ) (_hZinf : ∀ j, (Z j).Infinite)
    (hZ : Pairwise (fun i j => (Z i ∩ Z j).Finite))
    (A D : Fin n → B) (R : Fin m → Btilde)
    (hsep : ∀ j, ∀ μ ∈ M, ∀ ν ∈ N,
      (∃ i, ε ≤ |μ (Sum.inl '' ((A i).val ∩ Z j ∪ (D i).val ∩ (Z j)ᶜ)) -
        ν (Sum.inl '' ((A i).val ∩ Z j ∪ (D i).val ∩ (Z j)ᶜ))|) ∨
      (∃ l, ε ≤ |μ (Sum.inr '' (R l).val) - ν (Sum.inr '' (R l).val)|)) :
    PairedSeparated B Btilde M N :=
  haydon_finite_separation B Btilde hfinite M N A D R Z hZ ε hε hk hsep

/-- Lemma 4.7 with the infinite cylinder, positive infimum, all three
infinite sets, and positivity of both constants displayed explicitly. -/
theorem lemma_4_7_printed (C₀ : Set ℕ) (hC : (cylinder C₀).Infinite)
    (μ : ℕ → lp (fun _ : Point => ℝ) 1)
    (hnorm : ∀ n, ‖μ n‖ ≤ 1) (hanti : ∀ n k, μ n (k, false) = -μ n (k, true))
    (hb : 0 < ⨅ n, |μ n (n, false)|) :
    let b := ⨅ n, |μ n (n, false)|
    ∃ (J₀ J₁ J₂ : Set ℕ) (Z : Set Point) (a δ : ℝ),
      J₂ ⊆ J₁ ∧ J₁ ⊆ J₀ ∧ J₀ ⊆ C₀ ∧ J₀.Infinite ∧ J₁.Infinite ∧ J₂.Infinite ∧
      (J₀ \ J₁).Infinite ∧ (J₁ \ J₂).Infinite ∧ Splits J₁ Z ∧
      0 < a ∧ a ≥ b ∧ 0 < δ ∧ δ < b / 11 ∧
      (∀ n ∈ J₂, |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z) - 2 * a| < 3 * δ) ∧
      (∀ n ∈ J₁ \ J₂, |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z) + 2 * a| < 3 * δ) ∧
      (∀ n ∈ J₀ \ J₁, |mass (μ n) Z - mass (μ n) (cylinder J₁ \ Z)| < 3 * δ) := by
  have hC₀ : C₀.Infinite := fun h => hC (cylinder_finite h)
  obtain ⟨J₀, J₁, J₂, Z, a, δ, h₂₁, h₁₀, h₀C, h₂, h₁₂, h₀₁, hZ, ha, hδ, hδb, hp, hm, hz⟩ :=
    three_level_selection C₀ μ hC₀ ⟨hnorm, hanti, (positive_diagonal_iff μ).mpr hb⟩
  exact ⟨J₀, J₁, J₂, Z, a, δ, h₂₁, h₁₀, h₀C, (h₂.mono h₂₁).mono h₁₀, h₂.mono h₂₁,
    h₂, h₀₁, h₁₂, hZ, hb.trans_le ha, ha, hδ, hδb, hp, hm, hz⟩

end SigmaNonprimarity
