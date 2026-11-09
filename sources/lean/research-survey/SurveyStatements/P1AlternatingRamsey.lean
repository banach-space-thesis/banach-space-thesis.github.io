import SurveyStatements.P1ClosedRamsey
import SurveyStatements.P1RosenthalStabilization
import SurveyStatements.P1AlternatingScalarBranch

/-! The Ramsey selection of alternating functional patterns in the complex
Rosenthal proof. Finite ranks are the numbers of preceding elements. -/

noncomputable section
set_option autoImplicit false
open Filter Topology Set

namespace SurveyStatements.P1

theorem strictMono_finset_rank_image (ν : ℕ → ℕ) (hν : StrictMono ν)
    (G : Finset ℕ) (k : ℕ) :
    ((G.image ν).filter (fun j => j < ν k)).card =
      (G.filter (fun j => j < k)).card := by
  classical
  rw [Finset.filter_image]
  simp only [hν.lt_iff_lt]
  exact Finset.card_image_of_injective _ hν.injective

theorem strictMono_prefix_rank (ν : ℕ → ℕ) (hν : StrictMono ν)
    {n i : ℕ} (hi : i ≤ n) :
    (((Finset.range n).image ν).filter (fun j => j < ν i)).card = i := by
  rw [strictMono_finset_rank_image ν hν]
  have hfilter : (Finset.range n).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨h.trans_le hi, h⟩⟩
  rw [hfilter, Finset.card_range]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def HasAlternatingFunctionalPattern (s : ℕ → X) (ε M τ : ℝ) (G : Finset ℕ) : Prop :=
  ∃ f : X →L[ℂ] ℂ, ∃ z w : ℂ, ‖f‖ = 1 ∧ ‖z‖ ≤ M ∧ ε ≤ ‖w‖ ∧
    ∀ k ∈ G, ‖f (s k) -
      (z + if (G.filter (fun j => j < k)).card % 2 = 0 then 0 else w)‖ ≤ τ

theorem stable_scalar_obstruction_exists_alternating_patterns (s : ℕ → X)
    {ε M τ : ℝ} (hM : ∀ n, ‖s n‖ ≤ M) (hτ : 0 < τ)
    (hstable : ∀ κ : ℕ → ℕ, StrictMono κ → ¬ HasScalarTailDiameter (s ∘ κ) ε) :
    ∃ μ : ℕ → ℕ, StrictMono μ ∧
      ∀ G : Finset ℕ, HasAlternatingFunctionalPattern (s ∘ μ) ε M τ G := by
  classical
  let P : Finset ℕ → Prop := HasAlternatingFunctionalPattern s ε M τ
  have hbranch (N : Set ℕ) (_hN : N ⊆ univ) (hNinf : N.Infinite) :
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ (∀ n, ρ n ∈ N) ∧
        ∀ n, P ((Finset.range n).image ρ) := by
    obtain ⟨κ, hκ, hκN⟩ := infiniteSet_exists_strictMono_sequence N hNinf
    obtain ⟨f, hf, hosc⟩ :=
      not_scalar_tail_diameter_exists_unit_functional (s ∘ κ) (hstable κ hκ)
    let u : ℕ → ℂ := fun n => f (s (κ n))
    have hu (n : ℕ) : ‖u n‖ ≤ M := by
      exact (f.le_opNorm _).trans (by simpa only [hf, one_mul] using hM (κ n))
    have hosc' (B : ℕ) : ∃ i ≥ B, ∃ j ≥ B, ε ≤ ‖u i - u j‖ := by
      obtain ⟨i, hi, j, hj, hlt⟩ := hosc B
      exact ⟨i, hi, j, hj, hlt.le⟩
    obtain ⟨z, w, hzM, hwM, hzw, p, q, hp, hq, hz, hw⟩ :=
      bounded_complex_tail_oscillation_cluster_pair u hu hosc'
    obtain ⟨ν, hν, hclose⟩ := scalar_clusters_exists_alternating_branch u z w p q hp hq hz hw hτ
    let ρ : ℕ → ℕ := κ ∘ ν
    have hρ : StrictMono ρ := hκ.comp hν
    refine ⟨ρ, hρ, fun n => hκN (ν n), ?_⟩
    intro n
    refine ⟨f, z, w - z, hf, hzM, ?_, ?_⟩
    · simpa only [norm_sub_rev] using hzw
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      rw [strictMono_prefix_rank ρ hρ (Finset.mem_range.mp hi).le]
      have hc : ‖u (ν i) - (z + if i % 2 = 0 then 0 else w - z)‖ < τ := by
        convert hclose i using 1
        split_ifs <;> simp
      exact hc.le
  obtain ⟨L, hLU, hL, hgood⟩ :=
    closedRamsey_from_infinite_branches P univ Set.infinite_univ hbranch
  obtain ⟨μ, hμ, hμL⟩ := infiniteSet_exists_strictMono_sequence L hL
  refine ⟨μ, hμ, ?_⟩
  intro G
  have himage : (↑(G.image μ) : Set ℕ) ⊆ L := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    exact hμL k
  obtain ⟨f, z, w, hf, hz, hw, hpat⟩ := hgood (G.image μ) himage
  refine ⟨f, z, w, hf, hz, hw, ?_⟩
  intro k hk
  have h := hpat (μ k) (Finset.mem_image_of_mem μ hk)
  rw [strictMono_finset_rank_image μ hμ G k] at h
  exact h

end SurveyStatements.P1
