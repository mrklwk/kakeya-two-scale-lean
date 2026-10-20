module
public import KakeyaTwoScale.ConcreteRootDecomposition
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem sum_rpow_le_rpow_sum {ι : Type*} (S : Finset ι) (a : ι→ℝ) {p : ℝ}
    (hp : 1≤p) (ha : ∀i∈S, 0≤a i) :
    (∑i∈S, (a i)^p)≤(∑i∈S, a i)^p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Real.zero_rpow (show p≠0 by linarith)]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀j∈S, 0≤a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hs := Finset.sum_nonneg has
    have hh := NNReal.add_rpow_le_rpow_add (⟨a i,hai⟩:NNReal) (⟨∑j∈S, a j,hs⟩:NNReal) hp
    have hh' : (a i)^p+(∑j∈S, a j)^p≤(a i+∑j∈S, a j)^p := by exact_mod_cast hh
    exact (add_le_add le_rfl (ih has)).trans hh'

/-- Summing actual coarse original populations costs only the bounded visit
multiplicity. The number of occupied coarse blocks never appears. -/
theorem coarse_population_sum_le {d k N : ℕ}
    (Y : Finset (RootTuple d k (Fin N))) {delta : ℝ} (hd : 0<delta) (hd1 : delta≤1)
    (b u : Fin N→EuclideanSpace ℝ (Fin d)) (hu : ∀o, ‖u o‖=1)
    (hinc : ∀y∈Y, ∀j, (rootGridCube delta y.1 ∩ flatCylinder (b (y.2 j)) (u (y.2 j)) 1 delta).Nonempty)
    (domains : Finset (Fin d→ℤ)) (e : ℕ) :
    (∑a∈domains, delta^e*∑j : Fin k, (((coarseRootTuples Y delta a).image (fun y => y.2 j)).card:ℝ)) ≤
      ((13:ℝ)^d*k)*(delta^e*N) := by
  rw [←Finset.mul_sum,Finset.sum_comm]
  have hslot (j : Fin k) :
      (∑a∈domains, (((coarseRootTuples Y delta a).image (fun y => y.2 j)).card:ℝ))≤(13:ℝ)^d*N := by
    have hh := coarseRootTuples_record_sum Y hd hd1 b u hu hinc domains j
    have hc : (Y.image (fun y => y.2 j)).card≤N :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)
    exact_mod_cast hh.trans (Nat.mul_le_mul_left (13^d) hc)
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hslot j)) (pow_nonneg hd.le e)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    (show delta^e*(∑j : Fin k, ∑a∈domains, (((coarseRootTuples Y delta a).image (fun y => y.2 j)).card:ℝ))≤
      ((13:ℝ)^d*k)*(delta^e*N) by
      convert hh using 1
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sum_rpow_le_rpow_sum
#print axioms KakeyaTwoScale.coarse_population_sum_le
