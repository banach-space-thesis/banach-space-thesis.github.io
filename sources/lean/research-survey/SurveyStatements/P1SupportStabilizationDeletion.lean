import SurveyStatements.P1SupportStabilizationBase
import Mathlib.Topology.Order.OrderClosed

/-! The first, uniform one-coordinate deletion step in DOSZ Lemma 2.6.
The bad homogeneous alternative contradicts an actual `c₀` cluster limit. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Topology

namespace SurveyStatements.P1

def SupportDeletionGood (f : Set ℕ → ℕ → ℂ) (F : Finset ℕ) (δ : ℝ)
    (Q : Set ℕ) : Prop :=
  ‖f ((F : Set ℕ) ∪ (Q \ {sInf Q})) (sInf Q)‖ < δ

theorem supportDeletionGood_prefix_closed
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (F : Finset ℕ) (δ : ℝ) :
    ∀ ν : ℕ → ℕ, StrictMono ν → ¬ SupportDeletionGood f F δ (range ν) →
      ∃ N : ℕ, ∀ η : ℕ → ℕ, StrictMono η →
        (Finset.range N).image η = (Finset.range N).image ν →
          ¬ SupportDeletionGood f F δ (range η) := by
  classical
  intro ν hν hbad
  let R : Set ℕ := (F : Set ℕ) ∪ (range ν \ {sInf (range ν)})
  have hR : R.Infinite :=
    (support_tail_infinite _ (support_infinite_strictMono_range ν hν)).mono
      (subset_union_right)
  obtain ⟨r, hr⟩ := hf R hR
  refine ⟨max r 1, ?_⟩
  intro η hη hprefix
  have hfirst : η 0 = ν 0 :=
    support_prefix_eq_first ν η hν hη (by omega) hprefix
  have hmin : sInf (range η) = sInf (range ν) := by
    rw [support_strictMono_range_sInf η hη, support_strictMono_range_sInf ν hν]
    exact hfirst
  have hsame : f ((F : Set ℕ) ∪ (range η \ {sInf (range η)})) = f R := by
    apply hr _ ((support_tail_infinite _
      (support_infinite_strictMono_range η hη)).mono subset_union_right)
    intro i hi
    have hmem := support_prefix_eq_low_membership ν η hν hη hprefix i
      (hi.trans_le (le_max_left _ _))
    simp only [R, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    rw [hmin, hmem]
  intro hgood
  apply hbad
  change ‖f ((F : Set ℕ) ∪ (range η \ {sInf (range η)})) (sInf (range η))‖ < δ at hgood
  rw [hsame, hmin] at hgood
  exact hgood

theorem supportDeletionGood_bad_impossible
    (f : Set ℕ → ℕ → ℂ) (hcluster : SupportAssignmentSequentialC0Cluster f)
    (F : Finset ℕ) (δ : ℝ) (hδ : 0 < δ)
    (L : Set ℕ) (hL : L.Infinite)
    (hbad : ∀ Q : Set ℕ, Q ⊆ L → Q.Infinite →
      ¬ SupportDeletionGood f F δ Q) : False := by
  classical
  obtain ⟨l, hl, hlL⟩ := infiniteSet_exists_strictMono_sequence L hL
  let T : ℕ → Set ℕ := fun n => range (fun k => l (n + k + 1))
  have hT (n : ℕ) : (T n).Infinite := by
    apply support_infinite_strictMono_range
    intro i j hij
    exact hl (by omega)
  have hTL (n : ℕ) : T n ⊆ L := by
    rintro x ⟨k, rfl⟩
    exact hlL _
  have hTailGt (n i : ℕ) (hi : i ≤ n) : ∀ x ∈ T n, l i < x := by
    rintro x ⟨k, rfl⟩
    exact hl (by omega)
  have hbound (n i : ℕ) (hi : i ≤ n) :
      δ ≤ ‖f ((F : Set ℕ) ∪ T n) (l i)‖ := by
    let Q : Set ℕ := insert (l i) (T n)
    have hQ : Q.Infinite := (hT n).mono (subset_insert _ _)
    have hmin : sInf Q = l i := by
      apply le_antisymm
      · exact Nat.sInf_le (mem_insert _ _)
      · have hm := Nat.sInf_mem hQ.nonempty
        rcases hm with h | h
        · exact h ▸ le_rfl
        · exact (hTailGt n i hi _ h).le
    have hnot : l i ∉ T n := fun h => (hTailGt n i hi _ h).false
    have htail : Q \ {sInf Q} = T n := by
      ext x
      simp only [Q, hmin, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, hne⟩
        · exact False.elim (hne h)
        · exact h
      · intro h
        exact ⟨Or.inr h, fun hx => hnot (hx ▸ h)⟩
    have hb := hbad Q (by
      intro x hx
      rcases hx with h | h
      · exact h ▸ hlL i
      · exact hTL n h) hQ
    change ¬ ‖f ((F : Set ℕ) ∪ (Q \ {sInf Q})) (sInf Q)‖ < δ at hb
    rw [htail, hmin] at hb
    exact le_of_not_gt hb
  obtain ⟨g, μ, hμ, hg, hlim⟩ := hcluster
    (fun n => (F : Set ℕ) ∪ T n) (fun n => (hT n).mono subset_union_right)
  have hgbound (i : ℕ) : δ ≤ ‖g (l i)‖ := by
    apply ge_of_tendsto (hlim (l i)).norm
    filter_upwards [eventually_ge_atTop i] with n hn
    exact hbound (μ n) i (hn.trans (hμ.id_le n))
  have hzero : Tendsto (fun i => ‖g (l i)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hg.comp hl.tendsto_atTop).norm
  exact (not_le_of_gt hδ) (ge_of_tendsto' hzero hgbound)

theorem support_exists_uniform_deletion
    (f : Set ℕ → ℕ → ℂ) (hf : SupportAssignmentLocallyConstant f)
    (hcluster : SupportAssignmentSequentialC0Cluster f)
    (F : Finset ℕ) (δ : ℝ) (hδ : 0 < δ)
    (M : Set ℕ) (hM : M.Infinite) :
    ∃ L : Set ℕ, L ⊆ M ∧ L.Infinite ∧
      ∀ Q : Set ℕ, Q ⊆ L → Q.Infinite → SupportDeletionGood f F δ Q := by
  classical
  obtain ⟨L, hLM, hL, hgood | hbad⟩ := prefixClass_closedRamsey
    (SupportDeletionGood f F δ) (supportDeletionGood_prefix_closed f hf F δ) M hM
  · refine ⟨L, hLM, hL, ?_⟩
    intro Q hQL hQ
    obtain ⟨ν, hν, hνQ⟩ := support_infinite_enumeration Q hQ
    rw [← hνQ] at hQL ⊢
    exact hgood ν hν hQL
  · exfalso
    apply supportDeletionGood_bad_impossible f hcluster F δ hδ L hL
    intro Q hQL hQ
    obtain ⟨ν, hν, hνQ⟩ := support_infinite_enumeration Q hQ
    rw [← hνQ] at hQL ⊢
    exact hbad ν hν hQL

end SurveyStatements.P1
