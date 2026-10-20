module
public import KakeyaTwoScale.ConsecutiveSlopes
public import KakeyaTwoScale.Exponents

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical
open scoped BigOperators

def integerVectorProjection {n : ℕ} (i : ℕ) (v : (Fin n → ℤ) × (Fin n → ℤ)) : Fin n → ℤ :=
  v.1+(i:ℤ) • v.2

def rationalVector {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun j => (v j:ℚ)
def rationalVectorPair {n : ℕ} (v : (Fin n → ℤ) × (Fin n → ℤ)) : (Fin n → ℚ) × (Fin n → ℚ) :=
  (rationalVector v.1,rationalVector v.2)

theorem rationalVector_injective (n : ℕ) : Function.Injective (rationalVector (n:=n)) := by
  intro v w h
  funext j
  have hh := congrFun h j
  change (v j:ℚ) = (w j:ℚ) at hh
  exact_mod_cast hh

theorem rationalVectorPair_injective (n : ℕ) : Function.Injective (rationalVectorPair (n:=n)) := by
  intro v w h
  exact Prod.ext (rationalVector_injective n (congrArg Prod.fst h))
    (rationalVector_injective n (congrArg Prod.snd h))

theorem rationalVector_projection {n : ℕ} (i : ℕ) (v : (Fin n → ℤ) × (Fin n → ℤ)) :
    vectorProjection (i:ℚ) (rationalVectorPair v) = rationalVector (integerVectorProjection i v) := by
  funext j
  simp only [vectorProjection,rationalVectorPair,rationalVector,integerVectorProjection,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast]

theorem consecutive_integer_partition_625_373 :
    ∃ ell : ℕ, 2 ≤ ell ∧ ∀ n : ℕ,
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
      ∃ i : ℕ, i < ell ∧ fiberCardPartition G Prod.snd (252/373) ≤
        ((G.image (integerVectorProjection i)).card:ℝ)^(625/373:ℝ) := by
  obtain ⟨ell,hell,hcount⟩ := consecutive_vector_partition_625_373
  refine ⟨ell,hell,?_⟩
  intro n G
  let e := rationalVectorPair (n:=n)
  obtain ⟨i,hi,hh⟩ := hcount n (G.image e)
  have hv : ∀ v ∈ G, ∀ w ∈ G, (e v).2=(e w).2 ↔ v.2=w.2 := by
    intro v _ w _
    exact (rationalVector_injective n).eq_iff
  have hpart := fiberCardPartition_encoding G e Prod.snd Prod.snd
    (rationalVectorPair_injective n).injOn hv (252/373)
  have hcard : ((G.image e).image (vectorProjection (i:ℚ))).card =
      (G.image (integerVectorProjection i)).card := by
    rw [Finset.image_image]
    apply image_card_of_same_fibers
    intro v _ w _
    change vectorProjection (i:ℚ) (rationalVectorPair v) = vectorProjection (i:ℚ) (rationalVectorPair w) ↔ _
    rw [rationalVector_projection,rationalVector_projection]
    exact (rationalVector_injective n).eq_iff
  rw [hpart,hcard] at hh
  exact ⟨i,hi,hh⟩

theorem vertical_fiber_first_card {A B : Type*} [DecidableEq A] [DecidableEq B]
    (G : Finset (A × B)) (y : B) :
    ((G.filter (fun v => v.2=y)).image Prod.fst).card = (G.filter (fun v => v.2=y)).card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw he
  exact Prod.ext he ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm)

/-- Source arithmetic contract A, with one ell independent of dimension and
of the finite integer graph. Occupied fibers are counted by their actual
intercept sets. Empty graphs and dimension zero are included. -/
theorem arithmetic_counting_source :
    ∃ ell : ℕ, 2 ≤ ell ∧ ∀ m : ℕ,
      ∀ G : Finset ((Fin m → ℤ) × (Fin m → ℤ)),
      (∑ v ∈ G.image Prod.snd,
        (((G.filter (fun z => z.2=v)).image Prod.fst).card:ℝ)^(theta/a)) ≤
      (((Finset.range ell).sup (fun i => (G.image (integerVectorProjection i)).card):ℕ):ℝ)^(1/a) := by
  obtain ⟨ell,hell,hcount⟩ := consecutive_integer_partition_625_373
  refine ⟨ell,hell,?_⟩
  intro m G
  obtain ⟨i,hi,hh⟩ := hcount m G
  have hcard : (G.image (integerVectorProjection i)).card ≤
      (Finset.range ell).sup (fun j => (G.image (integerVectorProjection j)).card) :=
    Finset.le_sup (f := fun j => (G.image (integerVectorProjection j)).card) (Finset.mem_range.mpr hi)
  have hbound := hh.trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
    (show ((G.image (integerVectorProjection i)).card:ℝ) ≤
      (((Finset.range ell).sup (fun j => (G.image (integerVectorProjection j)).card):ℕ):ℝ) by exact_mod_cast hcard)
    (by norm_num : (0:ℝ) ≤ 625/373))
  simp only [vertical_fiber_first_card]
  norm_num only [theta,a] at ⊢
  exact hbound

end KakeyaTwoScale
#print axioms KakeyaTwoScale.rationalVector_injective
#print axioms KakeyaTwoScale.rationalVectorPair_injective
#print axioms KakeyaTwoScale.rationalVector_projection
#print axioms KakeyaTwoScale.consecutive_integer_partition_625_373
#print axioms KakeyaTwoScale.vertical_fiber_first_card
#print axioms KakeyaTwoScale.arithmetic_counting_source
