module
public import KakeyaTwoScale.WeightedMultilinearAssembly

@[expose] public section

open Set
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Distributive weighted assembly over independently labeled families. Real
weights are handled directly, including zeros and repeated geometric tubes. -/
theorem weighted_tuple_factor_sum {k : ℕ} (L : Fin k → ℕ)
    (w : ((j : Fin k) → Fin (L j)) → ℝ)
    (a s : (j : Fin k) → Fin (L j) → ℝ) (m A : ℝ)
    (ha : ∀j t, 0≤a j t)
    (hw : ∀f, w f*m≤A*∏j, s j (f j)) :
    (∑f, w f*(∏j, a j (f j)))*m≤A*∏j, (∑t, a j t*s j t) := by
  classical
  rw [Finset.sum_mul,Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  have hh := mul_le_mul_of_nonneg_right (hw f) (show 0≤∏j, a j (f j) from Finset.prod_nonneg (fun j _ => ha j (f j)))
  rw [Finset.prod_mul_distrib]
  nlinarith only [hh]

def cubeTubeWeight {n k : ℕ} (L : Fin k → ℕ)
    (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
    (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
    (a : (j : Fin k) → Fin (L j) → ℝ)
    (z : Fin (n+1) → ℤ) (j : Fin k) (t : Fin (L j)) : ℝ :=
  if (visibilityCube (fun i => (z i:ℝ)) ∩ infiniteLineTube (b j t) (WithLp.ofLp (u j t)) 1).Nonempty
  then a j t else 0

def cubeMultilinearMass {n k : ℕ} (L : Fin k → ℕ)
    (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
    (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
    (a : (j : Fin k) → Fin (L j) → ℝ) (z : Fin (n+1) → ℤ) : ℝ :=
  ∑f : (j : Fin k) → Fin (L j), tupleWedgeVolume (fun j => u j (f j))*
    ∏j, cubeTubeWeight L b u a z j (f j)

theorem cubeTubeWeight_nonneg {n k : ℕ} (L : Fin k → ℕ) (b u a)
    (ha : ∀j t, 0≤a j t) (z : Fin (n+1) → ℤ) (j : Fin k) (t : Fin (L j)) :
    0≤cubeTubeWeight L b u a z j t := by
  unfold cubeTubeWeight
  split_ifs
  · exact ha j t
  · exact le_rfl

theorem cubeMultilinearMass_nonneg {n k : ℕ} (L : Fin k → ℕ) (b u a)
    (ha : ∀j t, 0≤a j t) (z : Fin (n+1) → ℤ) :
    0≤cubeMultilinearMass L b u a z :=
  Finset.sum_nonneg (fun f _ => mul_nonneg (tupleWedgeVolume_nonneg _)
    (Finset.prod_nonneg (fun j _ => cubeTubeWeight_nonneg L b u a ha z j (f j))))

/-- Complete weighted finite-lattice multilinear estimate. All constants
precede the arbitrary finite cubes, independent labeled tube families and real
nonnegative weights. There is no separation or tube-length assumption. -/
theorem weighted_cube_multilinear (n k : ℕ) (hk : 2≤k) (hkn : k≤n+1) :
    ∃C : ℝ, 0≤C ∧ ∀(J : ℕ) (z : Fin J → Fin (n+1) → ℤ),
      Function.Injective z → ∀(L : Fin k → ℕ)
      (b : (j : Fin k) → Fin (L j) → Fin (n+1) → ℝ)
      (u : (j : Fin k) → Fin (L j) → EuclideanSpace ℝ (Fin (n+1)))
      (a : (j : Fin k) → Fin (L j) → ℝ), (∀j t, ‖u j t‖=1) → (∀j t, 0≤a j t) →
      (∑q, (cubeMultilinearMass L b u a (z q))^(1/((k-1:ℕ):ℝ)))≤
        C*(∏j, ∑t, a j t)^(1/((k-1:ℕ):ℝ)) := by
  classical
  obtain ⟨A,B,hA,hB,hfactor⟩ := actual_multilinear_factors n k hkn
  refine ⟨(A*B^k)^(1/((k-1:ℕ):ℝ)),Real.rpow_nonneg (mul_nonneg hA (pow_nonneg hB k)) _,?_⟩
  intro J z hz L b u a hu ha
  have hweight (q j t) := cubeTubeWeight_nonneg L b u a ha (z q) j t
  have hm := finite_multilinear_variational_bound hk
    (fun q => cubeMultilinearMass L b u a (z q))
    (fun q => cubeMultilinearMass_nonneg L b u a ha (z q)) A hA
    (fun j => B*(∑t, a j t)) (fun j => mul_nonneg hB (Finset.sum_nonneg (fun t _ => ha j t))) ?_
  · simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hm
    rw [← mul_assoc,Real.mul_rpow (mul_nonneg hA (pow_nonneg hB k))
      (Finset.prod_nonneg (fun j _ => Finset.sum_nonneg (fun t _ => ha j t)))] at hm
    exact hm
  intro m hm hmsum
  obtain ⟨S,hS,hSw,hSt⟩ := hfactor J z hz m hm hmsum
  let c := fun j q => ∑t, cubeTubeWeight L b u a (z q) j t*S q (u j t)
  refine ⟨c,fun j q => Finset.sum_nonneg (fun t _ => mul_nonneg (hweight q j t) (hS q _)),?_,?_⟩
  · intro q
    exact weighted_tuple_factor_sum L (fun f => tupleWedgeVolume (fun j => u j (f j)))
      (cubeTubeWeight L b u a (z q)) (fun j t => S q (u j t)) (m q) A
      (hweight q) (fun f => hSw q (fun j => u j (f j)))
  · intro j
    have ht (t : Fin (L j)) : (∑q, cubeTubeWeight L b u a (z q) j t*S q (u j t))≤a j t*B := by
      let I := Finset.univ.filter (fun q : Fin J =>
        (visibilityCube (fun i => (z q i:ℝ)) ∩ infiniteLineTube (b j t) (WithLp.ofLp (u j t)) 1).Nonempty)
      have hh := hSt I (b j t) (u j t) (hu j t) (fun q hq => (Finset.mem_filter.mp hq).2)
      have he : (∑q, cubeTubeWeight L b u a (z q) j t*S q (u j t))=
          a j t*(∑q∈I, S q (u j t)) := by
        simp only [cubeTubeWeight,I,Finset.sum_filter,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs <;> simp
      rw [he]
      exact mul_le_mul_of_nonneg_left hh (ha j t)
    change (∑q, ∑t, cubeTubeWeight L b u a (z q) j t*S q (u j t))≤_
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑t, a j t*B := Finset.sum_le_sum (fun t _ => ht t)
      _ = _ := by rw [← Finset.sum_mul]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.weighted_tuple_factor_sum
#print axioms KakeyaTwoScale.weighted_cube_multilinear
