import Posets.SzlenkIdealImage
import Mathlib.SetTheory.Ordinal.NaturalOps

/-! Last surviving point ranks for the actual Szlenk derivation. Natural
sums of two ranks control sets whose norm distance is bounded by the sum
of two continuous coordinate distances. -/

noncomputable section
open Set Topology
open scoped NaturalOps
namespace Posets
variable {𝕜 E F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem exists_szlenk_last_stage {ε : ℝ} {K : Set (WeakDual 𝕜 E)}
    {x : WeakDual 𝕜 E} (hx : x ∈ K) (κ : Ordinal)
    (hn : x ∉ szlenkIterate ε K κ) :
    ∃ r < κ, x ∈ szlenkIterate ε K r ∧ x ∉ szlenkIterate ε K (Order.succ r) := by
  induction κ using SuccOrder.limitRecOn with
  | isMin κ hκ =>
      obtain rfl := hκ.eq_bot
      exact False.elim (hn (by simpa using hx))
  | succ κ hκ ih =>
      by_cases hi : x ∈ szlenkIterate ε K κ
      · exact ⟨κ, Order.lt_succ κ, hi, hn⟩
      · obtain ⟨r, hr, hxr, hxr'⟩ := ih hi
        exact ⟨r, hr.trans (Order.lt_succ κ), hxr, hxr'⟩
  | isSuccLimit κ hκ ih =>
      rw [szlenkIterate_limit ε K κ hκ] at hn
      simp only [mem_iInter, not_forall] at hn
      obtain ⟨β, hβ⟩ := hn
      obtain ⟨r, hr, hxr, hxr'⟩ := ih β.val β.property hβ
      exact ⟨r, hr.trans β.property, hxr, hxr'⟩

theorem exists_szlenk_point_rank {ε : ℝ} {K : Set (WeakDual 𝕜 E)}
    {κ : Ordinal} (he : szlenkIterate ε K κ = ∅) :
    ∃ r : WeakDual 𝕜 E → Ordinal, ∀ x ∈ K,
      r x < κ ∧ ∀ β, x ∈ szlenkIterate ε K β ↔ β ≤ r x := by
  classical
  have hr : ∀ x : WeakDual 𝕜 E, ∃ r : Ordinal, x ∈ K →
      r < κ ∧ ∀ β, x ∈ szlenkIterate ε K β ↔ β ≤ r := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨r, hr, hxr, hxr'⟩ := exists_szlenk_last_stage hx κ (by rw [he]; simp)
      refine ⟨r, fun _ => ⟨hr, fun β => ⟨?_, ?_⟩⟩⟩
      · intro hβ
        by_contra hn
        exact hxr' (szlenkIterate_antitone ε K (Order.succ_le_of_lt (lt_of_not_ge hn)) hβ)
      · intro hβ
        exact szlenkIterate_antitone ε K hβ hxr
    · exact ⟨0, fun h => False.elim (hx h)⟩
  choose r hr using hr
  exact ⟨r, hr⟩

/-- A rank estimate for two coordinates. The ordinal closure assumption is
the only ordinal arithmetic needed in this analytic lemma. -/
theorem szlenkIterate_pair_empty
    (p : WeakDual 𝕜 G → WeakDual 𝕜 E) (q : WeakDual 𝕜 G → WeakDual 𝕜 F)
    (hp : Continuous p) (hq : Continuous q)
    {K : Set (WeakDual 𝕜 E)} {L : Set (WeakDual 𝕜 F)} {H : Set (WeakDual 𝕜 G)}
    (hK : IsClosed K) (hL : IsClosed L)
    (hpH : ∀ x ∈ H, p x ∈ K) (hqH : ∀ x ∈ H, q x ∈ L)
    (hd : ∀ x ∈ H, ∀ y ∈ H,
      ‖WeakDual.toStrongDual x - WeakDual.toStrongDual y‖ ≤
        ‖WeakDual.toStrongDual (p x) - WeakDual.toStrongDual (p y)‖ +
        ‖WeakDual.toStrongDual (q x) - WeakDual.toStrongDual (q y)‖)
    {δ : ℝ} {κ : Ordinal}
    (hκ : ∀ a < κ, ∀ b < κ, a ♯ b < κ)
    (hKe : szlenkIterate δ K κ = ∅) (hLe : szlenkIterate δ L κ = ∅) :
    szlenkIterate (2 * δ) H κ = ∅ := by
  classical
  obtain ⟨r, hr⟩ := exists_szlenk_point_rank hKe
  obtain ⟨s, hs⟩ := exists_szlenk_point_rank hLe
  have hi : ∀ β, ∀ x ∈ szlenkIterate (2 * δ) H β, β ≤ r (p x) ♯ s (q x) := by
    intro β
    induction β using SuccOrder.limitRecOn with
    | isMin β hβ =>
        obtain rfl := hβ.eq_bot
        intro x hx
        exact Ordinal.zero_le _
    | succ β hβ ih =>
        intro x hx
        have hxH := szlenkIterate_subset (2 * δ) H (Order.succ β) hx
        have hpx := hr (p x) (hpH x hxH)
        have hqx := hs (q x) (hqH x hxH)
        apply Order.succ_le_of_lt
        by_contra hn
        have hsum : r (p x) ♯ s (q x) ≤ β := le_of_not_gt hn
        have hpnot : p x ∉ szlenkDeriv δ (szlenkIterate δ K (r (p x))) := by
          rw [← szlenkIterate_succ]
          exact fun h => (not_le_of_gt (Order.lt_succ _)) ((hpx.2 _).mp h)
        have hqnot : q x ∉ szlenkDeriv δ (szlenkIterate δ L (s (q x))) := by
          rw [← szlenkIterate_succ]
          exact fun h => (not_le_of_gt (Order.lt_succ _)) ((hqx.2 _).mp h)
        have hpu : ∃ U, IsOpen U ∧ p x ∈ U ∧
            ∀ a ∈ szlenkIterate δ K (r (p x)) ∩ U,
            ∀ b ∈ szlenkIterate δ K (r (p x)) ∩ U,
              ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ δ := by
          by_contra h
          push_neg at h
          exact hpnot ⟨(hpx.2 _).mpr le_rfl, h⟩
        have hqu : ∃ U, IsOpen U ∧ q x ∈ U ∧
            ∀ a ∈ szlenkIterate δ L (s (q x)) ∩ U,
            ∀ b ∈ szlenkIterate δ L (s (q x)) ∩ U,
              ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ ≤ δ := by
          by_contra h
          push_neg at h
          exact hqnot ⟨(hqx.2 _).mpr le_rfl, h⟩
        obtain ⟨U, hU, hpxU, hsmallU⟩ := hpu
        obtain ⟨V, hV, hqxV, hsmallV⟩ := hqu
        let W := p ⁻¹' (U ∩ (szlenkIterate δ K (Order.succ (r (p x))))ᶜ) ∩
          q ⁻¹' (V ∩ (szlenkIterate δ L (Order.succ (s (q x))))ᶜ)
        have hW : IsOpen W :=
          ((hU.inter (szlenkIterate_isClosed δ hK _).isOpen_compl).preimage hp).inter
            ((hV.inter (szlenkIterate_isClosed δ hL _).isOpen_compl).preimage hq)
        have hxW : x ∈ W := by
          exact ⟨⟨hpxU, fun h => hpnot (by rwa [szlenkIterate_succ] at h)⟩,
            ⟨hqxV, fun h => hqnot (by rwa [szlenkIterate_succ] at h)⟩⟩
        have hstrata : ∀ y ∈ szlenkIterate (2 * δ) H β ∩ W,
            p y ∈ szlenkIterate δ K (r (p x)) ∧
              q y ∈ szlenkIterate δ L (s (q x)) := by
          intro y hy
          have hyH := szlenkIterate_subset (2 * δ) H β hy.1
          have hpy := hr (p y) (hpH y hyH)
          have hqy := hs (q y) (hqH y hyH)
          have hrle : r (p y) ≤ r (p x) := by
            by_contra h
            exact hy.2.1.2 ((hpy.2 _).mpr (Order.succ_le_of_lt (lt_of_not_ge h)))
          have hsle : s (q y) ≤ s (q x) := by
            by_contra h
            exact hy.2.2.2 ((hqy.2 _).mpr (Order.succ_le_of_lt (lt_of_not_ge h)))
          have hsumle := hsum.trans (ih y hy.1)
          constructor
          · apply (hpy.2 _).mpr
            by_contra h
            exact (not_lt_of_ge hsumle)
              (Ordinal.nadd_lt_nadd_of_lt_of_le (lt_of_not_ge h) hsle)
          · apply (hqy.2 _).mpr
            by_contra h
            exact (not_lt_of_ge hsumle)
              (Ordinal.nadd_lt_nadd_of_le_of_lt hrle (lt_of_not_ge h))
        rw [szlenkIterate_succ] at hx
        obtain ⟨a, ha, b, hb, hab⟩ := hx.2 W hW hxW
        have ha' := hstrata a ha
        have hb' := hstrata b hb
        have hpab := hsmallU (p a) ⟨ha'.1, ha.2.1.1⟩ (p b) ⟨hb'.1, hb.2.1.1⟩
        have hqab := hsmallV (q a) ⟨ha'.2, ha.2.2.1⟩ (q b) ⟨hb'.2, hb.2.2.1⟩
        have hab' := hd a (szlenkIterate_subset (2 * δ) H β ha.1)
          b (szlenkIterate_subset (2 * δ) H β hb.1)
        linarith
    | isSuccLimit β hβ ih =>
        intro x hx
        by_contra hn
        have hlt := hβ.succ_lt (lt_of_not_ge hn)
        have hh := ih _ hlt x (szlenkIterate_antitone (2 * δ) H hlt.le hx)
        exact (not_le_of_gt (Order.lt_succ _)) hh
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxH := szlenkIterate_subset (2 * δ) H κ hx
  exact (not_le_of_gt (hκ _ (hr _ (hpH x hxH)).1 _ (hs _ (hqH x hxH)).1)) (hi κ x hx)

end Posets
