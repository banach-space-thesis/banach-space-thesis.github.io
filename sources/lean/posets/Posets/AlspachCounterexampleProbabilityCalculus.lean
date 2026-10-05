import Posets.AlspachCounterexampleProbability

/-! Linear identities for the finite probability trees used in Alspach's
grafting construction. Equalities of vectors, rather than syntactic tree
equalities, allow the two averaging operations to be interchanged. -/

noncomputable section
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
namespace Posets
namespace AlspachProbability
variable {𝕜 K L X : Type*} [RCLike 𝕜]

theorem mem_support_map (p : AlspachProbability K) (f : K → L) (y : L) :
    y ∈ (p.map f).support ↔ ∃ x ∈ p.support, f x = y := by
  induction p with
  | point k => simp [map, support, eq_comm]
  | average p q hp hq =>
      simp only [map, support, Finset.mem_union, hp, hq]
      aesop

theorem mem_support_bind (p : AlspachProbability K) (f : K → AlspachProbability L) (y : L) :
    y ∈ (p.bind f).support ↔ ∃ x ∈ p.support, y ∈ (f x).support := by
  induction p with
  | point k => simp [bind, support]
  | average p q hp hq =>
      simp only [bind, support, Finset.mem_union, hp, hq]
      aesop

def mapLinear (f : K → L) : lp (fun _ : K => 𝕜) 1 →L[𝕜] lp (fun _ : L => 𝕜) 1 :=
  alspachSynthesis (fun k => lp.single 1 (f k) 1) 1 (fun _ => by simp [lp.norm_single])

@[simp] theorem mapLinear_single (f : K → L) (k : K) (c : 𝕜) :
    mapLinear f (lp.single 1 k c) = c • lp.single 1 (f k) 1 :=
  alspachSynthesis_single _ _ _ _ _

theorem mapLinear_vector (f : K → L) (p : AlspachProbability K) :
    mapLinear (𝕜 := 𝕜) f p.vector = (p.map f).vector := by
  induction p with
  | point k => simp [vector, map]
  | average p q hp hq => simp [vector, map, hp, hq]

def bindLinear (f : K → AlspachProbability L) :
    lp (fun _ : K => 𝕜) 1 →L[𝕜] lp (fun _ : L => 𝕜) 1 :=
  alspachSynthesis (fun k => (f k).vector) 1 (fun k => (f k).vector_norm_le)

theorem bindLinear_vector (f : K → AlspachProbability L) (p : AlspachProbability K) :
    bindLinear (𝕜 := 𝕜) f p.vector = (p.bind f).vector := by
  induction p with
  | point k => simp [vector, bindLinear, bind]
  | average p q hp hq => simp [vector, bind, hp, hq]

theorem vector_bind_point (p : AlspachProbability K) (f : K → L) :
    (p.bind (fun k => point (f k))).vector (𝕜 := 𝕜) = (p.map f).vector := by
  induction p with
  | point k => rfl
  | average p q hp hq => simp only [bind, map, vector, hp, hq]

theorem vector_bind_average (p : AlspachProbability K)
    (f g : K → AlspachProbability L) :
    (p.bind (fun k => average (f k) (g k))).vector (𝕜 := 𝕜) =
      (1 / 2 : 𝕜) • ((p.bind f).vector + (p.bind g).vector) := by
  induction p with
  | point k => rfl
  | average p q hp hq =>
      simp only [bind, vector, hp, hq]
      module

def tensorRightLinear (p : AlspachProbability K) (f : K → X → L) :
    lp (fun _ : X => 𝕜) 1 →L[𝕜] lp (fun _ : L => 𝕜) 1 :=
  alspachSynthesis (fun x => (p.map (fun k => f k x)).vector) 1
    (fun x => (p.map (fun k => f k x)).vector_norm_le)

theorem tensorRightLinear_vector (p : AlspachProbability K) (f : K → X → L)
    (q : AlspachProbability X) :
    tensorRightLinear (𝕜 := 𝕜) p f q.vector = (p.bind (fun k => q.map (f k))).vector := by
  induction q with
  | point x =>
      simp only [vector, tensorRightLinear, alspachSynthesis_single, one_smul, map]
      exact (vector_bind_point p _).symm
  | average q r hq hr =>
      simp only [vector, map_smul, map_add, hq, hr, map]
      exact (vector_bind_average p _ _).symm

end AlspachProbability
end Posets
