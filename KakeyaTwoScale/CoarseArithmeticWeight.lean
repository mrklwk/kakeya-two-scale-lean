module
public import KakeyaTwoScale.WholeGridVolume
public import KakeyaTwoScale.BrushSummation

@[expose] public section

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- A genuine cap on every occupied fiber gives the concave partition lower
bound, without an entropy or fiber-partition premise. -/
theorem capped_fiber_partition_lower {A B : Type*} [DecidableEq B]
    (G : Finset A) (f : A → B) (K p : ℝ) (hp : p ≤ 1)
    (hcap : ∀ y ∈ G.image f, ((G.filter (fun j => f j=y)).card:ℝ) ≤ K) :
    K^(p-1)*(G.card:ℝ) ≤ fiberCardPartition G f p := by
  have hcard : (G.card:ℝ) = ∑ y ∈ G.image f, ((G.filter (fun j => f j=y)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f G
  rw [hcard,Finset.mul_sum]
  exact Finset.sum_le_sum fun y hy => capped_weight_linearization _ K p (by positivity) (hcap y hy) hp

/-- The source's coarse arithmetic weight inequality for the actual lattice
parent axes. The positive constant is uniform in scale, common weight,
family and translations. Arithmetic volume and fiber lower bounds are proved. -/
theorem coarse_arithmetic_weight (n : ℕ) (B : ℝ) (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∀ (r u U : ℝ), 0 < r → 0 < u → 0 ≤ U →
      ∀ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty →
      (∀ v ∈ G.image Prod.snd, ((G.filter (fun j => j.2=v)).card:ℝ) ≤ B/u) →
      U ≤ 2*u*r^n*(G.card:ℝ) → ∀ z w : Fin n → ℝ,
      c*(r^n)^theta*U^a ≤
        volume.real (occupiedGridRegion G
          (fun p => latticePoint r p.1+z) (fun p => latticePoint r p.2+w) r
          (fun _ => Set.Icc (0:ℝ) 1))*u^theta := by
  obtain ⟨C,hC,hvolume⟩ := whole_lattice_segments_volume n
  refine ⟨C*B^(theta-a)/(2:ℝ)^a,by positivity,?_⟩
  intro r u U hr hu hU G hG hcap hmass z w
  have hv := hvolume r hr G hG z w
  have hp := capped_fiber_partition_lower G Prod.snd (B/u) (theta/a)
    (by norm_num [theta,a]) hcap
  have hpa := Real.rpow_le_rpow (by positivity : 0 ≤ (B/u)^(theta/a-1)*(G.card:ℝ))
    hp (by norm_num [a] : 0 ≤ a)
  rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul (by positivity)] at hpa
  have hex : (theta/a-1)*a=theta-a := by norm_num [theta,a]
  rw [hex] at hpa
  have hbase := (mul_le_mul_of_nonneg_left hpa (show 0 ≤ C*r^n by positivity)).trans hv
  have hbase' := mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hu.le theta)
  have hid : (B/u)^(theta-a)*u^theta = B^(theta-a)*u^a := by
    rw [Real.div_rpow hB.le hu.le,div_mul_eq_mul_div,mul_div_assoc,← Real.rpow_sub hu]
    rw [show theta-(theta-a)=a by ring]
  have hmain : C*r^n*B^(theta-a)*u^a*(G.card:ℝ)^a ≤
      volume.real (occupiedGridRegion G
        (fun p => latticePoint r p.1+z) (fun p => latticePoint r p.2+w) r
        (fun _ => Set.Icc (0:ℝ) 1))*u^theta := by
    calc
      _ = (C*r^n*((B/u)^(theta-a)*(G.card:ℝ)^a))*u^theta := by
        calc
          _ = C*r^n*(B^(theta-a)*u^a)*(G.card:ℝ)^a := by ring
          _ = C*r^n*((B/u)^(theta-a)*u^theta)*(G.card:ℝ)^a := by rw [hid]
          _ = _ := by ring
      _ ≤ _ := hbase'
  have hmasspow := Real.rpow_le_rpow hU hmass (by norm_num [a] : 0 ≤ a)
  have htarget := mul_le_mul_of_nonneg_left hmasspow
    (show 0 ≤ (C*B^(theta-a)/(2:ℝ)^a)*(r^n)^theta by positivity)
  apply le_trans htarget
  convert hmain using 1
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) hu.le]
  have hsum : (r^n)^theta*(r^n)^a=r^n := by
    rw [← Real.rpow_add (pow_pos hr n)]
    norm_num [theta,a]
  have htwo : (2:ℝ)^a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  calc
    _ = C*B^(theta-a)*((r^n)^theta*(r^n)^a)*u^a*(G.card:ℝ)^a := by field_simp
    _ = _ := by rw [hsum]; ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.capped_fiber_partition_lower
#print axioms KakeyaTwoScale.coarse_arithmetic_weight
