import Posets.WolfeTransportMass
import Posets.WolfeFamilies

/-! Exact transport of all Wolfe levels through a homeomorphism. Both the
weak-star limit condition and the closure of the union of child neighborhoods
are preserved. No loss of rank or mass threshold occurs. -/

noncomputable section
open Set Filter Topology Order
universe u
namespace Posets
variable {𝕜 : Type} [RCLike 𝕜] {K L : Type*}
variable [TopologicalSpace K] [TopologicalSpace L]

def wolfeNodeTransport (e : K ≃ₜ L) (p : WolfeNode 𝕜 K) : WolfeNode 𝕜 L :=
  (wolfeDualHomeomorph e p.1, e '' p.2)

@[simp] theorem wolfeNodeTransport_symm_apply (e : K ≃ₜ L) (p : WolfeNode 𝕜 K) :
    wolfeNodeTransport e.symm (wolfeNodeTransport e p) = p := by
  apply Prod.ext
  · exact (wolfeDualHomeomorph e).symm_apply_apply p.1
  · change e.symm '' (e '' p.2) = p.2
    rw [← Set.image_comp]
    simp only [Function.comp_def, e.symm_apply_apply, Set.image_id']

theorem WolfeChildren.homeomorph (e : K ≃ₜ L) {p : WolfeNode 𝕜 K}
    {c : ℕ → WolfeNode 𝕜 K} (hc : WolfeChildren p c) :
    WolfeChildren (wolfeNodeTransport e p) (fun n => wolfeNodeTransport e (c n)) := by
  refine ⟨(wolfeDualHomeomorph e).continuous.tendsto p.1 |>.comp hc.1, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_image_of_injective e.injective (hc.2.1 hij)
  · change closure (⋃ n, e '' (c n).2) ⊆ e '' p.2
    rw [← Set.image_iUnion, ← e.image_closure]
    exact Set.image_mono hc.2.2

variable [LocallyCompactSpace K] [LocallyCompactSpace L] [T2Space K] [T2Space L]

theorem wolfeBase_homeomorph (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L) (hK : JLMS.IsScattered K)
    (hL : JLMS.IsScattered L) (e : K ≃ₜ L) {ε : ℝ}
    {B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))} {p : WolfeNode 𝕜 K}
    (hp : p ∈ wolfeBase M ε B) :
    wolfeNodeTransport e p ∈ wolfeBase N ε (wolfeDualHomeomorph e '' B) := by
  refine ⟨⟨p.1, hp.1, rfl⟩, e.isOpenMap p.2 hp.2.1, ?_⟩
  change ε ≤ wolfeMass N (wolfeDualHomeomorph e p.1) (e '' p.2)
  rw [wolfeMass_homeomorph M N hK hL e p.1 hp.2.1]
  exact hp.2.2

theorem wolfeFamily_homeomorph (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L) (hK : JLMS.IsScattered K)
    (hL : JLMS.IsScattered L) (e : K ≃ₜ L) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) :
    ∀ p ∈ wolfeFamily M ε B α,
      wolfeNodeTransport e p ∈ wolfeFamily N ε (wolfeDualHomeomorph e '' B) α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro p hp
    rw [wolfeFamily_zero] at hp ⊢
    exact wolfeBase_homeomorph M N hK hL e hp
  | succ α ih =>
    intro p hp
    obtain ⟨hp, c, hc, hch⟩ := (mem_wolfeFamily_succ M ε B α p).mp hp
    exact (mem_wolfeFamily_succ N ε _ α _).mpr
      ⟨wolfeBase_homeomorph M N hK hL e hp,
        fun n => wolfeNodeTransport e (c n), fun n => ih (c n) (hc n), hch.homeomorph e⟩
  | limit α hα ih =>
    intro p hp
    obtain ⟨hp, a, ha, hcof, c, hc, hch⟩ := (mem_wolfeFamily_limit M ε B hα p).mp hp
    exact (mem_wolfeFamily_limit N ε _ hα _).mpr
      ⟨wolfeBase_homeomorph M N hK hL e hp, a, ha, hcof,
        fun n => wolfeNodeTransport e (c n),
        fun n => ih (a n).val (a n).property (c n) (hc n), hch.homeomorph e⟩

theorem wolfeFamily_homeomorph_iff (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L) (hK : JLMS.IsScattered K)
    (hL : JLMS.IsScattered L) (e : K ≃ₜ L) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) (p : WolfeNode 𝕜 K) :
    wolfeNodeTransport e p ∈ wolfeFamily N ε (wolfeDualHomeomorph e '' B) α ↔
      p ∈ wolfeFamily M ε B α := by
  refine ⟨?_, wolfeFamily_homeomorph M N hK hL e ε B α p⟩
  intro hp
  have h := wolfeFamily_homeomorph N M hL hK e.symm ε _ α _ hp
  have hset : wolfeDualHomeomorph e.symm '' (wolfeDualHomeomorph e '' B) = B := by
    change (wolfeDualHomeomorph e).symm '' (wolfeDualHomeomorph e '' B) = B
    rw [← Set.image_comp]
    simp only [Function.comp_def, Homeomorph.symm_apply_apply, Set.image_id']
  simpa only [hset, wolfeNodeTransport_symm_apply] using h

theorem wolfeFamily_homeomorph_nonempty_iff (M : JLMS.AtomicDualModel 𝕜 K)
    (N : JLMS.AtomicDualModel 𝕜 L) (hK : JLMS.IsScattered K)
    (hL : JLMS.IsScattered L) (e : K ≃ₜ L) (ε : ℝ)
    (B : Set (WeakDual 𝕜 (JLMS.CZero 𝕜 K))) (α : Ordinal.{u}) :
    (wolfeFamily N ε (wolfeDualHomeomorph e '' B) α).Nonempty ↔
      (wolfeFamily M ε B α).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨wolfeNodeTransport e.symm p, ?_⟩
    apply (wolfeFamily_homeomorph_iff M N hK hL e ε B α _).mp
    have hnode : wolfeNodeTransport e (wolfeNodeTransport e.symm p) = p :=
      wolfeNodeTransport_symm_apply e.symm p
    rwa [hnode]
  · rintro ⟨p, hp⟩
    exact ⟨wolfeNodeTransport e p, wolfeFamily_homeomorph M N hK hL e ε B α p hp⟩

end Posets
