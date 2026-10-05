import ThesisCommon.Analysis.DyadicSubtreeOscillation

/-! A genuine fusion of successively selected subtrees. At every node the
oscillation on its entire selected descendant cone is bounded by the given
level budget. No branch convergence or operator conclusion is assumed. -/
noncomputable section
namespace ThesisCommon
variable {K : Type*} [PseudoMetricSpace K]

structure DyadicOscillationState (f : DyadicTreeNode → K) (δ : ℕ → ℝ) where
  level : ℕ
  tree : DyadicSubtreeEmbedding
  bound : ∀ s t, dist (f (tree s)) (f (tree t)) < δ level

namespace DyadicOscillationState
variable (f : DyadicTreeNode → K) (hf : TotallyBounded (Set.range f))
  (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n)

def initial : DyadicOscillationState f δ where
  level := 0
  tree := dyadicOscillationSubtree f hf (δ 0) (hδ 0)
  bound := dyadicOscillationSubtree_bound f hf (δ 0) (hδ 0)

def refine (r : DyadicOscillationState f δ) (b : Bool) : DyadicOscillationState f δ :=
  let g := r.tree.comp (DyadicSubtreeEmbedding.cone [b])
  let hg : TotallyBounded (Set.range (fun s => f (g s))) :=
    hf.subset (by rintro _ ⟨s, rfl⟩; exact ⟨g s, rfl⟩)
  let e := dyadicOscillationSubtree (fun s => f (g s)) hg (δ (r.level + 1)) (hδ _)
  { level := r.level + 1
    tree := g.comp e
    bound := dyadicOscillationSubtree_bound (fun s => f (g s)) hg (δ (r.level + 1)) (hδ _) }

@[simp] theorem refine_level (r : DyadicOscillationState f δ) (b : Bool) :
    (refine f hf δ hδ r b).level = r.level + 1 := rfl

theorem refine_tree_range (r : DyadicOscillationState f δ) (b : Bool) (s : DyadicTreeNode) :
    ∃ t, (refine f hf δ hδ r b).tree s = r.tree t := by
  exact ⟨_, rfl⟩

theorem refine_root_prefix (r : DyadicOscillationState f δ) (b : Bool) :
    (r.tree [] ++ [b]).IsPrefix ((refine f hf δ hδ r b).tree []) := by
  change (r.tree [] ++ [b]).IsPrefix (r.tree ([b] ++ _))
  exact (r.tree.split_prefix [] b).trans
    ((r.tree.prefix_iff _ _).mpr (List.prefix_append [b] _))

theorem fold_level (r : DyadicOscillationState f δ) (s : DyadicTreeNode) :
    (s.foldl (refine f hf δ hδ) r).level = r.level + s.length := by
  induction s generalizing r with
  | nil => simp
  | cons b s ih => simp only [List.foldl_cons, ih, refine_level, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 s.length]

theorem fold_tree_range (r : DyadicOscillationState f δ) (s t : DyadicTreeNode) :
    ∃ u, (s.foldl (refine f hf δ hδ) r).tree t = r.tree u := by
  induction s generalizing r with
  | nil => exact ⟨t, rfl⟩
  | cons b s ih =>
    obtain ⟨u, hu⟩ := ih (refine f hf δ hδ r b)
    obtain ⟨v, hv⟩ := refine_tree_range f hf δ hδ r b u
    exact ⟨v, hu.trans hv⟩

end DyadicOscillationState

theorem exists_dyadic_subtree_descendant_oscillation (f : DyadicTreeNode → K)
    (hf : TotallyBounded (Set.range f)) (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ e : DyadicSubtreeEmbedding, ∀ s t, s.IsPrefix t →
      dist (f (e s)) (f (e t)) < δ s.length := by
  let step := DyadicOscillationState.refine f hf δ hδ
  let node (r : DyadicOscillationState f δ) := r.tree []
  let r := DyadicOscillationState.initial f hf δ hδ
  let e := dyadicExpansionEmbedding step node
    (DyadicOscillationState.refine_root_prefix f hf δ hδ) r
  refine ⟨e, ?_⟩
  intro s t hst
  obtain ⟨v, rfl⟩ := hst
  change dist (f ((s.foldl step r).tree [])) (f (((s ++ v).foldl step r).tree [])) < _
  rw [List.foldl_append]
  obtain ⟨u, hu⟩ := DyadicOscillationState.fold_tree_range f hf δ hδ (s.foldl step r) v []
  rw [hu]
  have h := (s.foldl step r).bound [] u
  have hlevel : (s.foldl step r).level = s.length := by
    simpa only [r, DyadicOscillationState.initial, zero_add] using
      DyadicOscillationState.fold_level f hf δ hδ r s
  simpa only [hlevel] using h

end ThesisCommon
