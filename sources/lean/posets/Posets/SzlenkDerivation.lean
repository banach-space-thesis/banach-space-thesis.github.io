import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Basic

/-! The actual weak-star Szlenk derivative. Norm distances are measured in
the strong dual; neighborhoods retain the weak-star topology. -/

noncomputable section
open Set Topology
namespace Posets
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Remove every relatively weak-star open part of norm diameter at most ε.
The pairwise-distance form also makes sense for unbounded sets. -/
def szlenkDeriv (ε : ℝ) (K : Set (WeakDual 𝕜 E)) : Set (WeakDual 𝕜 E) :=
  {x | x ∈ K ∧ ∀ U : Set (WeakDual 𝕜 E), IsOpen U → x ∈ U →
    ∃ a ∈ K ∩ U, ∃ b ∈ K ∩ U,
      ε < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖}

theorem szlenkDeriv_subset (ε : ℝ) (K : Set (WeakDual 𝕜 E)) :
    szlenkDeriv ε K ⊆ K := fun _ hx => hx.1

theorem szlenkDeriv_mono (ε : ℝ) :
    Monotone (szlenkDeriv (𝕜 := 𝕜) (E := E) ε) := by
  intro K L hKL x hx
  refine ⟨hKL hx.1, ?_⟩
  intro U hU hxU
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 U hU hxU
  exact ⟨a, ⟨hKL ha.1, ha.2⟩, b, ⟨hKL hb.1, hb.2⟩, hab⟩

theorem szlenkDeriv_antitone_scale (K : Set (WeakDual 𝕜 E)) :
    Antitone (fun ε => szlenkDeriv ε K) := by
  intro ε δ hεδ x hx
  refine ⟨hx.1, ?_⟩
  intro U hU hxU
  obtain ⟨a, ha, b, hb, hab⟩ := hx.2 U hU hxU
  exact ⟨a, ha, b, hb, hεδ.trans_lt hab⟩

@[simp] theorem szlenkDeriv_empty (ε : ℝ) :
    szlenkDeriv ε (∅ : Set (WeakDual 𝕜 E)) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr (fun _ hx => hx.1)

theorem szlenkDeriv_isClosed (ε : ℝ) {K : Set (WeakDual 𝕜 E)} (hK : IsClosed K) :
    IsClosed (szlenkDeriv ε K) := by
  classical
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  by_cases hxK : x ∈ K
  · have hn : ¬ ∀ U : Set (WeakDual 𝕜 E), IsOpen U → x ∈ U →
        ∃ a ∈ K ∩ U, ∃ b ∈ K ∩ U,
          ε < ‖WeakDual.toStrongDual a - WeakDual.toStrongDual b‖ :=
      fun h => hx ⟨hxK, h⟩
    push_neg at hn
    obtain ⟨U, hU, hxU, hsmall⟩ := hn
    refine ⟨U, ?_, hU, hxU⟩
    intro y hy hyd
    obtain ⟨a, ha, b, hb, hab⟩ := hyd.2 U hU hy
    exact (not_lt_of_ge (hsmall a ha b hb)) hab
  · exact ⟨Kᶜ, (fun _ hy hd => hy hd.1), hK.isOpen_compl, hxK⟩

theorem szlenkDeriv_isCompact (ε : ℝ) {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K) :
    IsCompact (szlenkDeriv ε K) :=
  hK.of_isClosed_subset (szlenkDeriv_isClosed ε hK.isClosed) (szlenkDeriv_subset ε K)

/-- Transfinite iteration uses intersections at limit stages. -/
def szlenkIterate (ε : ℝ) (K : Set (WeakDual 𝕜 E)) (α : Ordinal) :
    Set (WeakDual 𝕜 E) :=
  @transfiniteIterate (OrderDual (Set (WeakDual 𝕜 E))) _ (szlenkDeriv ε)
    Ordinal _ _ _ α K

@[simp] theorem szlenkIterate_zero (ε : ℝ) (K : Set (WeakDual 𝕜 E)) :
    szlenkIterate ε K 0 = K :=
  transfiniteIterate_bot (I := OrderDual (Set (WeakDual 𝕜 E))) _ _

theorem szlenkIterate_succ (ε : ℝ) (K : Set (WeakDual 𝕜 E)) (α : Ordinal) :
    szlenkIterate ε K (Order.succ α) = szlenkDeriv ε (szlenkIterate ε K α) :=
  transfiniteIterate_succ (I := OrderDual (Set (WeakDual 𝕜 E))) _ _ _ (not_isMax α)

theorem szlenkIterate_limit (ε : ℝ) (K : Set (WeakDual 𝕜 E)) (α : Ordinal)
    (hα : Order.IsSuccLimit α) :
    szlenkIterate ε K α = ⋂ β : Set.Iio α, szlenkIterate ε K β.val :=
  transfiniteIterate_limit (I := OrderDual (Set (WeakDual 𝕜 E))) _ _ _ hα

theorem szlenkIterate_antitone (ε : ℝ) (K : Set (WeakDual 𝕜 E)) :
    Antitone (szlenkIterate ε K) :=
  monotone_transfiniteIterate (I := OrderDual (Set (WeakDual 𝕜 E))) _ _
    (szlenkDeriv_subset ε)

theorem szlenkIterate_subset (ε : ℝ) (K : Set (WeakDual 𝕜 E)) (α : Ordinal) :
    szlenkIterate ε K α ⊆ K := by
  simpa only [szlenkIterate_zero] using szlenkIterate_antitone ε K (Ordinal.zero_le α)

theorem szlenkIterate_isClosed (ε : ℝ) {K : Set (WeakDual 𝕜 E)} (hK : IsClosed K)
    (α : Ordinal) : IsClosed (szlenkIterate ε K α) := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
      obtain rfl := hα.eq_bot
      simpa using hK
  | succ α hα ih =>
      rw [szlenkIterate_succ]
      exact szlenkDeriv_isClosed ε ih
  | isSuccLimit α hα ih =>
      rw [szlenkIterate_limit ε K α hα]
      exact isClosed_iInter (fun β => ih β.val β.property)

theorem szlenkIterate_isCompact (ε : ℝ) {K : Set (WeakDual 𝕜 E)} (hK : IsCompact K)
    (α : Ordinal) : IsCompact (szlenkIterate ε K α) :=
  hK.of_isClosed_subset (szlenkIterate_isClosed ε hK.isClosed α)
    (szlenkIterate_subset ε K α)

theorem szlenkIterate_mono (ε : ℝ) (α : Ordinal) :
    Monotone (fun K : Set (WeakDual 𝕜 E) => szlenkIterate ε K α) := by
  induction α using SuccOrder.limitRecOn with
  | isMin α hα =>
      obtain rfl := hα.eq_bot
      simpa using (monotone_id : Monotone (fun K : Set (WeakDual 𝕜 E) => K))
  | succ α hα ih =>
      intro K L hKL
      simpa only [szlenkIterate_succ] using szlenkDeriv_mono ε (ih hKL)
  | isSuccLimit α hα ih =>
      intro K L hKL
      simp only [szlenkIterate_limit ε _ α hα]
      exact Set.iInter_mono (fun β => ih β.val β.property hKL)

@[simp] theorem szlenkIterate_empty (ε : ℝ) (α : Ordinal) :
    szlenkIterate ε (∅ : Set (WeakDual 𝕜 E)) α = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr
    (fun _ hx => szlenkIterate_subset ε ∅ α hx)

/-- An index bound is expressed by vanishing of the actual derivatives;
no ordinal-valued rank or undefined-rank convention is assumed. -/
def HasSzlenkBound (K : Set (WeakDual 𝕜 E)) (α : Ordinal) : Prop :=
  ∀ ε : ℝ, 0 < ε → szlenkIterate ε K α = ∅

theorem HasSzlenkBound.mono {K : Set (WeakDual 𝕜 E)} {α β : Ordinal}
    (h : HasSzlenkBound K α) (hαβ : α ≤ β) : HasSzlenkBound K β := by
  intro ε hε
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm := szlenkIterate_antitone ε K hαβ hx
  rw [h ε hε] at hm
  exact hm

theorem HasSzlenkBound.subset {K L : Set (WeakDual 𝕜 E)} {α : Ordinal}
    (h : HasSzlenkBound L α) (hKL : K ⊆ L) : HasSzlenkBound K α := by
  intro ε hε
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm := szlenkIterate_mono ε α hKL hx
  change x ∈ szlenkIterate ε L α at hm
  rw [h ε hε] at hm
  exact hm

end Posets
