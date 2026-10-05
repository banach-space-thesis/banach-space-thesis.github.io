import Posets.CountableOrdinalPFPCanonicalNodes

/-! The canonical ordinal cells form a genuine rank-labelled Wolfe family
for every continuous row map. The children are constructed explicitly from
Cantor--Bendixson accumulation; no preservation assumption is used. -/

noncomputable section
open Set Topology Order
universe u
namespace Posets
open ThesisCommon
variable {𝕜 : Type*} [RCLike 𝕜]

theorem ordinalTowerNode_mem_rankedWolfeFamily {θ γ : Ordinal.{u}}
    (hcθ : θ.card ≤ Cardinal.aleph0) (hcγ : γ.card ≤ Cardinal.aleph0)
    (hθ : θ ∈ ordinalTowerLevel θ γ)
    (μ : Iic θ → WeakDual 𝕜 (JLMS.CZero 𝕜 (Iic θ))) (hμ : Continuous μ)
    (α : Ordinal.{u}) :
    ∀ p : OrdinalTowerNode θ γ, p.level.val = α →
      p ∈ rankedWolfeFamily (OrdinalTowerNode.toWolfeNode μ)
        (fun p => p.level.val) Set.univ Set.univ α := by
  classical
  induction α using Ordinal.limitRecOn with
  | zero =>
      intro p hp
      exact (mem_rankedWolfeFamily_zero _ _ _ _ _).mpr ⟨mem_univ _, hp, mem_univ _⟩
  | succ α ih =>
      intro p hp
      have hαγ : α ≤ γ := (le_succ α).trans (hp ▸ p.level.property)
      have hθα : θ ∈ ordinalTowerLevel θ α := ordinalTowerLevel_antitone θ hαγ hθ
      have hpa : p.point.val ∈ derivedSet (ordinalTowerLevel θ α) := by
        simpa only [ordinalTowerLevel, hp, ordinalDerived_succ] using p.mem_level
      obtain ⟨y, hy, hyH, hd, ht, hclosure⟩ := ordinal_exists_canonical_children θ
        (fun _ => ordinalTowerLevel θ α) (fun _ => ordinalTowerLevel_isCompact θ α)
        (fun _ => hθα) p.point ((Ordinal.card_le_card p.point.property).trans hcθ)
        (fun _ => hpa) p.cell_isClopen p.point_mem_cell
      choose hyA hyiso using fun n => (hy n).2
      let c : ℕ → OrdinalTowerNode θ γ := fun n =>
        ⟨⟨α, hαγ⟩, y n, hyA n, hyiso n⟩
      apply (mem_rankedWolfeFamily_succ _ _ _ _ α p).mpr
      refine ⟨mem_univ _, hp, c, (fun n => ih (c n) rfl), ?_⟩
      exact ⟨hμ.continuousAt.tendsto.comp ht, hd, hclosure⟩
  | limit α hα ih =>
      intro p hp
      have hαγ : α ≤ γ := hp ▸ p.level.property
      obtain ⟨a, ha, hcof⟩ := countable_limit_exists_strictMono_cofinal hα
        ((Ordinal.card_le_card hαγ).trans hcγ)
      have hag (n : ℕ) : (a n).val ≤ γ := (a n).property.le.trans hαγ
      have hθa (n : ℕ) : θ ∈ ordinalTowerLevel θ (a n).val :=
        ordinalTowerLevel_antitone θ (hag n) hθ
      have hpa (n : ℕ) : p.point.val ∈ derivedSet (ordinalTowerLevel θ (a n).val) := by
        change p.point.val ∈ derivedSet (ordinalDerived (Iic θ) (a n).val)
        rw [← ordinalDerived_succ]
        apply ordinalDerived_antitone isClosed_Iic (hα.succ_lt (a n).property).le
        simpa only [ordinalTowerLevel, hp] using p.mem_level
      obtain ⟨y, hy, hyH, hd, ht, hclosure⟩ := ordinal_exists_canonical_children θ
        (fun n => ordinalTowerLevel θ (a n).val) (fun n => ordinalTowerLevel_isCompact θ (a n).val)
        hθa p.point ((Ordinal.card_le_card p.point.property).trans hcθ)
        hpa p.cell_isClopen p.point_mem_cell
      choose hyA hyiso using fun n => (hy n).2
      let c : ℕ → OrdinalTowerNode θ γ := fun n =>
        ⟨⟨(a n).val, hag n⟩, y n, hyA n, hyiso n⟩
      apply (mem_rankedWolfeFamily_limit _ _ _ _ hα p).mpr
      refine ⟨mem_univ _, hp, a, ha, hcof, c, (fun n => ih _ (a n).property (c n) rfl), ?_⟩
      exact ⟨hμ.continuousAt.tendsto.comp ht, hd, hclosure⟩

end Posets
