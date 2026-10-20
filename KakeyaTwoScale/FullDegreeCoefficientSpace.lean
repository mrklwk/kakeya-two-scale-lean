module
public import KakeyaTwoScale.PolynomialCoefficients
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- The full total-degree coefficient index set, rather than a monomial box. -/
def FullDegreeIndex (N D : ℕ) :=
  {f : Fin N → Fin (D+1) // ∑ i, (f i).val ≤ D}

instance (N D : ℕ) : Fintype (FullDegreeIndex N D) := inferInstanceAs
  (Fintype {f : Fin N → Fin (D+1) // ∑ i, (f i).val ≤ D})

def fullDegreeMonomial (N D : ℕ) (j : FullDegreeIndex N D) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (j.val i).val)

theorem fullDegreeMonomial_injective (N D : ℕ) : Function.Injective (fullDegreeMonomial N D) := by
  intro j k h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun f : Fin N →₀ ℕ => f i) h

theorem fullDegreeMonomial_degree (N D : ℕ) (j : FullDegreeIndex N D) :
    (fullDegreeMonomial N D j).sum (fun _ e => e) ≤ D := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact j.property

/-- Every monomial of degree at most D occurs exactly once in the full space. -/
theorem fullDegreeMonomial_complete {N D : ℕ} (e : Fin N →₀ ℕ)
    (he : e.sum (fun _ k => k) ≤ D) : ∃ j, fullDegreeMonomial N D j=e := by
  have hs : ∑ i, e i ≤ D := by
    rw [Finsupp.sum_fintype _ _ (by simp)] at he
    exact he
  let f : Fin N → Fin (D+1) := fun i => ⟨e i,Nat.lt_succ_of_le
    ((Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)).trans hs)⟩
  refine ⟨⟨f,hs⟩,?_⟩
  ext i
  rfl

/-- The box is used only as an injective dimension witness in the full space. -/
theorem fullDegree_card_ge_box {N : ℕ} (hN : 0<N) (L : ℕ) :
    (L+1)^N ≤ Fintype.card (FullDegreeIndex N (N*L)) := by
  let f : (Fin N → Fin (L+1)) → FullDegreeIndex N (N*L) := fun j =>
    ⟨fun i => ⟨(j i).val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ (j i).isLt).trans
      (Nat.le_mul_of_pos_left L hN))⟩,by
      calc
        ∑ i, (j i).val ≤ ∑ _i : Fin N, L := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (j i).isLt)
        _ = N*L := by simp⟩
  have hf : Function.Injective f := by
    intro j k h
    funext i
    apply Fin.ext
    exact congrArg (fun q : FullDegreeIndex N (N*L) => (q.val i).val) h
  simpa using Fintype.card_le_of_injective f hf

/-- Exact degree selection for the full coefficient sphere. The root estimate
is stated without real rounding loss; it includes a zero label count. -/
theorem full_degree_space_above_count {N : ℕ} (hN : 0<N) (M : ℕ) :
    ∃ D : ℕ, M < Fintype.card (FullDegreeIndex N D) ∧ D^N ≤ N^N*M := by
  let L := Nat.nthRoot N M
  refine ⟨N*L,?_,?_⟩
  · exact (Nat.lt_pow_nthRoot_add_one hN.ne' M).trans_le (fullDegree_card_ge_box hN L)
  · rw [mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (Or.inl hN.ne'))

/-- A literal Fin-indexed enumeration of the full monomial space, as required
by the existing intrinsic spherical-average API. -/
def fullDegreeFinMonomial (N D : ℕ) : Fin (Fintype.card (FullDegreeIndex N D)) → (Fin N →₀ ℕ) :=
  fullDegreeMonomial N D ∘ (Fintype.equivFin (FullDegreeIndex N D)).symm

theorem fullDegreeFinMonomial_injective (N D : ℕ) : Function.Injective (fullDegreeFinMonomial N D) :=
  (fullDegreeMonomial_injective N D).comp (Fintype.equivFin _).symm.injective

theorem fullDegreeFinMonomial_degree (N D : ℕ) (i) :
    (fullDegreeFinMonomial N D i).sum (fun _ e => e) ≤ D := fullDegreeMonomial_degree N D _

theorem fullDegreeFinMonomial_complete {N D : ℕ} (e : Fin N →₀ ℕ)
    (he : e.sum (fun _ k => k) ≤ D) : ∃ i, fullDegreeFinMonomial N D i=e := by
  obtain ⟨j,hj⟩ := fullDegreeMonomial_complete e he
  exact ⟨Fintype.equivFin _ j,by simpa [fullDegreeFinMonomial] using hj⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.fullDegreeMonomial_complete
#print axioms KakeyaTwoScale.fullDegree_card_ge_box
#print axioms KakeyaTwoScale.full_degree_space_above_count
#print axioms KakeyaTwoScale.fullDegreeFinMonomial_injective
#print axioms KakeyaTwoScale.fullDegreeFinMonomial_degree
#print axioms KakeyaTwoScale.fullDegreeFinMonomial_complete
