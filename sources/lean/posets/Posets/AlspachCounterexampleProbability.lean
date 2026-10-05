import Posets.AlspachCounterexampleForest

/-! Finite dyadic probability rows and their private-support readout.
Alspach's specialized construction only uses Dirac masses and averages of
two probabilities. Encoding these operations directly keeps positivity,
finite support and the norm-one bound explicit, for real and complex scalars. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets

inductive AlspachProbability (K : Type*) where
  | point : K → AlspachProbability K
  | average : AlspachProbability K → AlspachProbability K → AlspachProbability K

namespace AlspachProbability
variable {𝕜 I K L : Type*} [RCLike 𝕜]

def map (f : K → L) : AlspachProbability K → AlspachProbability L
  | point k => point (f k)
  | average p q => average (p.map f) (q.map f)

def bind (f : K → AlspachProbability L) : AlspachProbability K → AlspachProbability L
  | point k => f k
  | average p q => average (p.bind f) (q.bind f)

def support : AlspachProbability K → Finset K
  | point k => {k}
  | average p q => p.support ∪ q.support

def vector : AlspachProbability K → lp (fun _ : K => 𝕜) 1
  | point k => lp.single 1 k 1
  | average p q => (1 / 2 : 𝕜) • (p.vector + q.vector)

theorem vector_norm_le (p : AlspachProbability K) : ‖p.vector (𝕜 := 𝕜)‖ ≤ 1 := by
  induction p with
  | point k => simp [vector, lp.norm_single]
  | average p q hp hq =>
      change ‖(1 / 2 : 𝕜) • (p.vector + q.vector)‖ ≤ 1
      rw [norm_smul]
      have hn : ‖(1 / 2 : 𝕜)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
      rw [hn]
      have hs := norm_add_le (p.vector (𝕜 := 𝕜)) q.vector
      linarith

theorem vector_eq_zero_of_not_mem_support (p : AlspachProbability K) {k : K}
    (hk : k ∉ p.support) : p.vector (𝕜 := 𝕜) k = 0 := by
  induction p with
  | point j => simp only [support, Finset.mem_singleton] at hk; simp [vector, hk]
  | average p q hp hq =>
      simp only [support, Finset.mem_union, not_or] at hk
      simp [vector, hp hk.1, hq hk.2]

end AlspachProbability

variable {𝕜 I K : Type*} [RCLike 𝕜]

def alspachOwnerColumn (owner : K → Option I) (k : K) : lp (fun _ : I => 𝕜) 1 :=
  (owner k).elim 0 (fun i => lp.single 1 i 1)

theorem alspachOwnerColumn_norm_le (owner : K → Option I) (k : K) :
    ‖alspachOwnerColumn (𝕜 := 𝕜) owner k‖ ≤ 1 := by
  unfold alspachOwnerColumn
  cases owner k <;> simp [lp.norm_single]

def alspachOwnerRead (owner : K → Option I) :
    lp (fun _ : K => 𝕜) 1 →L[𝕜] lp (fun _ : I => 𝕜) 1 :=
  alspachSynthesis (alspachOwnerColumn owner) 1 (alspachOwnerColumn_norm_le owner)

theorem alspachOwnerRead_norm_le (owner : K → Option I) :
    ‖alspachOwnerRead (𝕜 := 𝕜) owner‖ ≤ 1 :=
  alspachSynthesis_norm_le _ zero_le_one _

@[simp] theorem alspachOwnerRead_single (owner : K → Option I) (k : K) (c : 𝕜) :
    alspachOwnerRead owner (lp.single 1 k c) = c • alspachOwnerColumn owner k :=
  alspachSynthesis_single _ _ _ _ _

theorem alspachOwnerRead_probability (owner : K → Option I)
    (p : AlspachProbability K) (i : I)
    (hp : ∀ k ∈ p.support, owner k = some i) :
    alspachOwnerRead (𝕜 := 𝕜) owner p.vector = lp.single 1 i 1 := by
  induction p with
  | point k =>
      have hk := hp k (Finset.mem_singleton_self k)
      simp [AlspachProbability.vector, alspachOwnerColumn, hk]
  | average p q ihp ihq =>
      have hp' : ∀ k ∈ p.support, owner k = some i :=
        fun k hk => hp k (Finset.mem_union_left _ hk)
      have hq' : ∀ k ∈ q.support, owner k = some i :=
        fun k hk => hp k (Finset.mem_union_right _ hk)
      change alspachOwnerRead owner ((1 / 2 : 𝕜) • (p.vector + q.vector)) = _
      rw [map_smul, map_add, ihp hp', ihq hq']
      module

/-- Concrete disjoint private probabilities provide the readout required
by the forest estimate. The owner function records the private support. -/
def alspachForestOfProbabilities (parent : I → Option I) (depth : I → ℕ)
    (hdepth : ∀ i j, parent i = some j → depth j < depth i)
    (privateRow row : I → AlspachProbability K) (owner : K → Option I)
    (howner : ∀ i k, k ∈ (privateRow i).support → owner k = some i)
    (hroot : ∀ i, parent i = none → row i = privateRow i)
    (hchild : ∀ i j, parent i = some j →
      row i = .average (privateRow i) (row j)) :
    AlspachForestRows 𝕜 I (lp (fun _ : K => 𝕜) 1) where
  parent := parent
  depth := depth
  parent_lt := hdepth
  privateRow i := (privateRow i).vector
  row i := (row i).vector
  read := alspachOwnerRead owner
  read_norm_le := alspachOwnerRead_norm_le owner
  read_private i := alspachOwnerRead_probability owner (privateRow i) i (howner i)
  root_row i hi := congrArg AlspachProbability.vector (hroot i hi)
  child_row i j hij := congrArg AlspachProbability.vector (hchild i j hij)
  row_norm_le i := (row i).vector_norm_le

end Posets
