import Posets.WolfeMass
import ThesisCommon.Analysis.OrdinalDerived

/-! Wolfe's transfinite families, with actual weak-star convergence and atomic
variation mass. The successor and limit clauses follow Alspach, *Operators on
C(ω^α) which do not preserve C(ω^α)*, Definition 3.1 (1996 preprint, p. 11).
The model parameter is the proved atomic dual representation, not a preservation
assumption. The family definition itself applies at every ordinal; the countable
cofinal sequences in the limit clause are explicit. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 K : Type*} [RCLike 𝕜] [TopologicalSpace K]

abbrev WolfeNode (𝕜 K : Type*) [RCLike 𝕜] [TopologicalSpace K] :=
  WeakDual 𝕜 (JLMS.CZero 𝕜 K) × Set K

def wolfeBase (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) : Set (WolfeNode 𝕜 K) :=
  {p | p.1 ∈ B ∧ IsOpen p.2 ∧ ε ≤ wolfeMass M p.1 p.2}

/-- The common topological conditions on a sequence of children. The closure
of the entire union, as printed in Definition 3.1, must stay inside the parent. -/
def WolfeChildren (p : WolfeNode 𝕜 K) (c : ℕ → WolfeNode 𝕜 K) : Prop :=
  Tendsto (fun n => (c n).1) atTop (𝓝 p.1) ∧
    Pairwise (fun i j => Disjoint (c i).2 (c j).2) ∧ closure (⋃ n, (c n).2) ⊆ p.2

theorem WolfeChildren.child_subset {p : WolfeNode 𝕜 K} {c : ℕ → WolfeNode 𝕜 K}
    (hc : WolfeChildren p c) (n : ℕ) : (c n).2 ⊆ p.2 :=
  (subset_iUnion (fun n => (c n).2) n).trans (subset_closure.trans hc.2.2)

def wolfeFamily (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) :
    Set (WolfeNode 𝕜 K) :=
  Ordinal.limitRecOn α (wolfeBase M ε B)
    (fun _ P => {p | p ∈ wolfeBase M ε B ∧
      ∃ c : ℕ → WolfeNode 𝕜 K, (∀ n, c n ∈ P) ∧ WolfeChildren p c})
    (fun α _ P => {p | p ∈ wolfeBase M ε B ∧
      ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧
        ∃ c : ℕ → WolfeNode 𝕜 K,
          (∀ n, c n ∈ P (a n).val (a n).property) ∧ WolfeChildren p c})

@[simp] theorem wolfeFamily_zero (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) :
    wolfeFamily M ε B (0 : Ordinal.{u}) = wolfeBase M ε B := by
  simp [wolfeFamily]

theorem mem_wolfeFamily_succ (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u})
    (p : WolfeNode 𝕜 K) : p ∈ wolfeFamily M ε B (succ α) ↔
      p ∈ wolfeBase M ε B ∧ ∃ c : ℕ → WolfeNode 𝕜 K,
        (∀ n, c n ∈ wolfeFamily M ε B α) ∧ WolfeChildren p c := by
  simp [wolfeFamily]

theorem mem_wolfeFamily_limit (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) {α : Ordinal.{u}} (hα : IsSuccLimit α)
    (p : WolfeNode 𝕜 K) : p ∈ wolfeFamily M ε B α ↔
      p ∈ wolfeBase M ε B ∧
      ∃ a : ℕ → Iio α, StrictMono (fun n => (a n).val) ∧
        (∀ β < α, ∃ n, β ≤ (a n).val) ∧
        ∃ c : ℕ → WolfeNode 𝕜 K,
          (∀ n, c n ∈ wolfeFamily M ε B (a n).val) ∧ WolfeChildren p c := by
  unfold wolfeFamily
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]
  rfl

theorem wolfeFamily_subset_base (M : JLMS.AtomicDualModel 𝕜 K) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) :
    wolfeFamily M ε B α ⊆ wolfeBase M ε B := by
  induction α using Ordinal.limitRecOn with
  | zero => simp
  | succ α _ => exact fun p hp => ((mem_wolfeFamily_succ M ε B α p).mp hp).1
  | limit α hα _ => exact fun p hp => ((mem_wolfeFamily_limit M ε B hα p).mp hp).1

theorem wolfeFamily_mono (M : JLMS.AtomicDualModel 𝕜 K)
    {ε δ : ℝ} (hδε : δ ≤ ε)
    {B C : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))} (hBC : B ⊆ C)
    (α : Ordinal.{u}) : wolfeFamily M ε B α ⊆ wolfeFamily M δ C α := by
  have hb : wolfeBase M ε B ⊆ wolfeBase M δ C :=
    fun _ hp => ⟨hBC hp.1, hp.2.1, hδε.trans hp.2.2⟩
  induction α using Ordinal.limitRecOn with
  | zero => simpa using hb
  | succ α ih =>
      intro p hp
      obtain ⟨hp, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B α p).mp hp
      exact (mem_wolfeFamily_succ M δ C α p).mpr ⟨hb hp, c, fun n => ih (hc n), hch⟩
  | limit α hα ih =>
      intro p hp
      obtain ⟨hp, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hα p).mp hp
      exact (mem_wolfeFamily_limit M δ C hα p).mpr
        ⟨hb hp, a, ha, hcof, c, fun n => ih (a n).val (a n).property (hc n), hch⟩

/-- Every Wolfe level projects into the corresponding Cantor--Bendixson
derivative of the weak-star closed set of measures. The nonconstant-child
argument uses finite variation, not a distinctness assumption on the children. -/
theorem wolfeFamily_subset_ordinalDerived (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) {B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))}
    (hB : IsClosed B) (α : Ordinal.{u}) :
    ∀ p ∈ wolfeFamily M ε B α, p.1 ∈ ThesisCommon.ordinalDerived B α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro p hp
      simpa using (wolfeFamily_subset_base M ε B 0 hp).1
  | succ α ih =>
      intro p hp
      obtain ⟨_, c, hc, hconv, hdisj, _⟩ := (mem_wolfeFamily_succ M ε B α p).mp hp
      rw [ThesisCommon.ordinalDerived_succ]
      exact wolfeSequence_mem_derivedSet M (fun n => (c n).1) (fun n => (c n).2)
        hdisj hε (fun n => (wolfeFamily_subset_base M ε B α (hc n)).2.2)
        hconv (fun n => ih (c n) (hc n))
  | limit α hα ih =>
      intro p hp
      obtain ⟨_, a, ha, hcof, c, hc, hconv, _, _⟩ :=
        (mem_wolfeFamily_limit M ε B hα p).mp hp
      rw [ThesisCommon.ordinalDerived_limit B hα]
      apply mem_iInter₂.mpr
      intro β hβ
      obtain ⟨n₀, hn₀⟩ := hcof β hβ
      apply (ThesisCommon.isClosed_ordinalDerived hB β).mem_of_tendsto hconv
      filter_upwards [eventually_ge_atTop n₀] with n hn
      exact ThesisCommon.ordinalDerived_antitone hB (hn₀.trans (ha.monotone hn))
        (ih (a n).val (a n).property (c n) (hc n))

theorem wolfeFamily_empty_of_ordinalDerived_empty (M : JLMS.AtomicDualModel 𝕜 K)
    {ε : ℝ} (hε : 0 < ε) {B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))}
    (hB : IsClosed B) {α : Ordinal.{u}} (hα : ThesisCommon.ordinalDerived B α = ∅) :
    wolfeFamily M ε B α = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have := wolfeFamily_subset_ordinalDerived M hε hB α p hp
  simp only [hα, mem_empty_iff_false] at this

end Posets
