module
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Metric Module
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Dimension-sharp sphere packing. The power is k for a sphere in a
(k+1)-dimensional normed space. Annulus volume, not full-ball volume, gives
this power. The coefficient is independent of the norm and direction family. -/
theorem sphere_packing_bound {X J : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (k : ℕ) (hdim : finrank ℝ X=k+1) (G : Finset J) (u : J → X)
    {r : ℝ} (hr : 0 < r) (hrone : r ≤ 1)
    (hu : ∀ j ∈ G, ‖u j‖=1)
    (hsep : ∀ j ∈ G, ∀ l ∈ G, j ≠ l → r ≤ dist (u j) (u l)) :
    (G.card:ℝ)*r^k ≤ 2*(k+1:ℝ)*2^k*3^k := by
  borelize X
  let mu : Measure X := Measure.addHaar
  let t : ℝ := r/3
  have ht : 0 < t := by dsimp [t]; positivity
  have htone : t ≤ 1/3 := by dsimp [t]; linarith
  have hinner : 0 < 1-t := by linarith
  have houter : 0 < 1+t := by linarith
  let U := ⋃ j ∈ G, ball (u j) t
  let A := ball (0:X) (1+t) \ ball (0:X) (1-t)
  have hdisjoint : Set.PairwiseDisjoint (↑G : Set J) (fun j => ball (u j) t) := by
    intro j hj l hl hne
    apply ball_disjoint_ball
    have hh := hsep j hj l hl hne
    dsimp [t]; linarith
  have hsub : U ⊆ A := by
    intro x hx
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion₂.mp hx
    have hx' : ‖x-u j‖ < t := by simpa [dist_eq_norm] using hx
    have hup := norm_le_norm_add_norm_sub x (u j)
    have hlow := norm_le_norm_add_norm_sub (u j) x
    rw [hu j hj,norm_sub_rev (u j) x] at hlow
    rw [hu j hj] at hup
    constructor
    · simpa [mem_ball,dist_zero_right] using (show ‖x‖ < 1+t by linarith)
    · simpa [mem_ball,dist_zero_right] using (show ¬ ‖x‖ < 1-t by linarith)
  have hfinite : mu (ball (0:X) (1+t)) ≠ ⊤ := measure_ball_lt_top.ne
  have hAfin : mu A ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hfinite
  have hvol (x : X) (s : ℝ) (hs : 0 < s) :
      mu.real (ball x s)=s^(k+1)*mu.real (ball (0:X) 1) := by
    rw [Measure.real,mu.addHaar_ball_of_pos x hs,hdim,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hU : mu.real U=(G.card:ℝ)*t^(k+1)*mu.real (ball (0:X) 1) := by
    rw [show U=⋃ j ∈ G, ball (u j) t from rfl,
      measureReal_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)]
    simp only [hvol _ t ht,Finset.sum_const,nsmul_eq_mul]
    ring
  have hA : mu.real A=((1+t)^(k+1)-(1-t)^(k+1))*mu.real (ball (0:X) 1) := by
    rw [show A=ball (0:X) (1+t) \ ball (0:X) (1-t) from rfl,
      measureReal_sdiff (ball_subset_ball (by linarith)) measurableSet_ball hfinite,
      hvol _ _ houter,hvol _ _ hinner]
    ring
  have hunitpos : 0 < mu.real (ball (0:X) 1) :=
    ENNReal.toReal_pos (measure_ball_pos mu (0:X) (by norm_num)).ne' measure_ball_lt_top.ne
  have hm := measureReal_mono hsub hAfin
  rw [hU,hA] at hm
  have hbase := (mul_le_mul_iff_left₀ hunitpos).mp hm
  have habs := abs_pow_sub_pow_le (a:=1+t) (b:=1-t) (n:=k+1)
  rw [abs_of_pos houter,abs_of_pos hinner,max_eq_left (by linarith),Nat.add_sub_cancel,
    show 1+t-(1-t)=2*t by ring,abs_of_pos (by positivity : 0 < 2*t)] at habs
  have hpow : (1+t)^k ≤ (2:ℝ)^k := by gcongr; linarith
  have hpowmul := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2*t)*(k+1:ℝ) by positivity)
  have hdiff : (1+t)^(k+1)-(1-t)^(k+1) ≤ 2*t*(k+1:ℝ)*2^k :=
    (le_abs_self _).trans (habs.trans (by simpa using hpowmul))
  have hsmall : (G.card:ℝ)*t^k ≤ 2*(k+1:ℝ)*2^k := by
    apply (mul_le_mul_iff_left₀ ht).mp
    have hh := hbase.trans hdiff
    rw [pow_succ] at hh
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_right hsmall (show (0:ℝ) ≤ 3^k by positivity)
  have he : t^k*(3:ℝ)^k=r^k := by rw [← mul_pow]; congr 1; dsimp [t]; ring
  calc
    _ = (G.card:ℝ)*t^k*3^k := by rw [mul_assoc,he]
    _ ≤ _ := hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.sphere_packing_bound
