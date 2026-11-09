import SurveyStatements.P1SuppressionCrossEvaluation
import SurveyStatements.P1SuppressionWitnessColors
import SurveyStatements.P1SupportStabilization
import SurveyStatements.P1WeakNullDualClusters
import SurveyStatements.P1ThinFamilyRamsey
import SurveyStatements.P1MatchingOrder

/-! Assembly of support stabilization, bounded-palette thin-family Ramsey,
and finite set matching into the genuine unit-modulus suppression
contradiction. The only inputs are actual finite witnesses selected on each
infinite set, with their proved finite-prefix and preference properties. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators Classical

namespace SurveyStatements.P1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem nonempty_initialSegment_sInf_eq (C D : Finset ℕ)
    (hC : C.Nonempty) (hD : D.Nonempty) (hCD : FinsetIsInitialSegment C D) :
    sInf (C : Set ℕ) = sInf (D : Set ℕ) := by
  have hc : sInf (C : Set ℕ) ∈ C := Nat.sInf_mem (Finset.coe_nonempty.mpr hC)
  have hd : sInf (D : Set ℕ) ∈ D := Nat.sInf_mem (Finset.coe_nonempty.mpr hD)
  have hle : sInf (D : Set ℕ) ≤ sInf (C : Set ℕ) := Nat.sInf_le (hCD.1 hc)
  apply le_antisymm _ hle
  by_cases hdC : sInf (D : Set ℕ) ∈ C
  · exact Nat.sInf_le hdC
  · exact (hCD.2 _ hc _ hd hdC).le

theorem unitSuppressionWitness_assignment_contradiction
    (e : ℕ → X) (he : ∀ n, ‖e n‖ = 1)
    (hp : ∀ N M : ℕ, N ≤ M → ∀ a : ℕ → ℂ,
      (1 / 2 : ℝ) * ‖sequencePartialSum e a N‖ ≤ ‖sequencePartialSum e a M‖)
    (hweak : ∀ f : StrongDual ℂ X, Tendsto (fun i => f (e i)) atTop (𝓝 0))
    (A : Finset ℂ) (hA : ∀ α ∈ A, ‖α‖ = 1)
    (φ : Set ℕ → UnitSuppressionWitness e A)
    (hvalid : ∀ P : Set ℕ, P.Infinite → ((φ P).coefficients.support : Set ℕ) ⊆ P)
    (hlocal : ∀ P : Set ℕ, P.Infinite → ∃ r : ℕ, ∀ Q : Set ℕ, Q.Infinite →
      (∀ i : ℕ, i < r → (i ∈ P ↔ i ∈ Q)) → φ Q = φ P)
    (hsame : ∀ P Q : Set ℕ, P.Infinite → Q.Infinite →
      (φ P).coefficients.support = (φ Q).coefficients.support → φ P = φ Q)
    (hthin : IsThinFiniteFamily {s : Finset ℕ | ∃ P : Set ℕ,
      P.Infinite ∧ s = (φ P).coefficients.support}) : False := by
  let f : Set ℕ → ℕ → ℂ := fun P i => (φ P).functional (e i)
  have hf : SupportAssignmentLocallyConstant f := by
    intro P hP
    obtain ⟨r, hr⟩ := hlocal P hP
    refine ⟨r, ?_⟩
    intro Q hQ hagree
    dsimp only [f]
    rw [hr Q hQ hagree]
  have hcluster : SupportAssignmentSequentialC0Cluster f := by
    intro P hP
    obtain ⟨g, hg, ν, hν, hlim⟩ := weakNull_boundedDual_coordinate_cluster e hweak
      (fun n => (φ (P n)).functional) (fun n => (φ (P n)).functional_bound)
    exact ⟨g, ν, hν, hg, hlim⟩
  obtain ⟨N, _, hN, hoffN⟩ := support_assignment_stabilization f hf hcluster
    1 (by norm_num) univ Set.infinite_univ
  let 𝒜 : Set (Finset ℕ) := {s | ∃ P : Set ℕ, P.Infinite ∧ s = (φ P).coefficients.support}
  let rep : Finset ℕ → UnitSuppressionWitness e A := fun s =>
    if hs : s ∈ 𝒜 then φ hs.choose else φ univ
  have hrepS (s : Finset ℕ) (hs : s ∈ 𝒜) : (rep s).coefficients.support = s := by
    simp only [rep, dif_pos hs]
    exact hs.choose_spec.2.symm
  have hrep (P : Set ℕ) (hP : P.Infinite) : rep (φ P).coefficients.support = φ P := by
    have hs : (φ P).coefficients.support ∈ 𝒜 := ⟨P, hP, rfl⟩
    simp only [rep, dif_pos hs]
    exact hsame hs.choose P hs.choose_spec.1 hP hs.choose_spec.2.symm
  have hne (s : Finset ℕ) (hs : s ∈ 𝒜) : s.Nonempty := by
    rw [← hrepS s hs]
    exact (rep s).selected_nonempty.mono (rep s).selected_subset
  let c : Finset ℕ → ℕ := fun s => (rep s).color
  have hbound (s : Finset ℕ) (hs : s ∈ 𝒜) :
      c s ≤ unitSuppressionColorBudget A (sInf (s : Set ℕ)) := by
    change (rep s).color ≤ _
    simpa only [hrepS s hs] using (rep s).color_bound
  obtain ⟨B, hBN, hB, hcolor⟩ := thin_family_boundedColorRamsey 𝒜 hthin hne
    (unitSuppressionColorBudget A) c hbound N hN
  let F : Set ℕ → Finset ℕ := fun P => (φ P).selected
  have hF : IsLocallyConstantFiniteAssignment F := by
    intro P hP
    obtain ⟨r, hr⟩ := hlocal P hP
    refine ⟨r, ?_⟩
    intro Q hQ hagree
    dsimp only [F]
    rw [hr Q hQ hagree]
  have hFsupp (P : Set ℕ) (hP : P.Infinite) : (F P : Set ℕ) ⊆ P :=
    fun i hi => hvalid P hP ((φ P).selected_subset hi)
  obtain ⟨L, M, hLB, hMB, hL, hM, hmatch, hinter⟩ := finiteSet_matching_lemma F hF hFsupp B hB
  have hmin : sInf ((φ L).coefficients.support : Set ℕ) =
      sInf ((φ M).coefficients.support : Set ℕ) := by
    rw [(φ L).first_support, (φ M).first_support]
    rcases hmatch with h | h
    · exact nonempty_initialSegment_sInf_eq _ _ (φ L).selected_nonempty (φ M).selected_nonempty h
    · exact (nonempty_initialSegment_sInf_eq _ _ (φ M).selected_nonempty (φ L).selected_nonempty h).symm
  have hcolors : (φ L).color = (φ M).color := by
    have h := hcolor (φ L).coefficients.support ⟨L, hL, rfl⟩
      (φ M).coefficients.support ⟨M, hM, rfl⟩
      ((hvalid L hL).trans hLB) ((hvalid M hM).trans hMB) hmin
    simpa only [c, hrep L hL, hrep M hM] using h
  have hoff (P Q : Set ℕ) (hP : P.Infinite) (hPB : P ⊆ B) (hQB : Q ⊆ B)
      (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ Q \ P) :
      ∑ i ∈ S, ‖(φ P).functional (e i)‖ ≤ 1 :=
    hoffN P (hPB.trans hBN) hP S (fun i hi =>
      ⟨hBN (hQB (hS hi).1), (hS hi).2⟩)
  rcases hmatch with h | h
  · have hinterL : L ∩ M = ((φ L).selected : Set ℕ) := by
      rw [hinter]
      exact Set.inter_eq_left.mpr (show ((φ L).selected : Set ℕ) ⊆ (φ M).selected from h.1)
    obtain ⟨hcoeff, hvalue⟩ := (φ M).phase_eq_of_color_eq (φ L) hcolors.symm
    exact matched_unitSuppressionWitness_contradiction hA he hp (φ L) (φ M) L M
      (hvalid M hM) h.1 hinterL hcoeff hvalue
      ((φ L).mass_near_of_color_eq (φ M) hcolors) (hoff L M hL hLB hMB)
  · have hinterM : M ∩ L = ((φ M).selected : Set ℕ) := by
      rw [Set.inter_comm, hinter, Set.inter_comm]
      exact Set.inter_eq_left.mpr (show ((φ M).selected : Set ℕ) ⊆ (φ L).selected from h.1)
    obtain ⟨hcoeff, hvalue⟩ := (φ L).phase_eq_of_color_eq (φ M) hcolors
    exact matched_unitSuppressionWitness_contradiction hA he hp (φ M) (φ L) M L
      (hvalid L hL) h.1 hinterM hcoeff hvalue
      ((φ M).mass_near_of_color_eq (φ L) hcolors.symm) (hoff M L hM hMB hLB)

end SurveyStatements.P1
