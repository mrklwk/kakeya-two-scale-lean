module
public import KakeyaTwoScale.ConcreteStoppedOptimization
public import KakeyaTwoScale.ActualUniformStoppingError
public import KakeyaTwoScale.SharpProjectiveCount

@[expose] public section

open Filter
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual stopping with every logarithmic error and packing constraint discharged
at a uniform scale threshold. No degree constraint or analytic estimate is assumed. -/
theorem eventually_concrete_stopped_optimization (n k m : ℕ) (hk : 2≤k) (hn : n+1=m+k)
    (alpha Ccap epsilon : ℝ) (hp : 0<alpha) (hp1 : alpha≤1)
    (hα : 1/(k:ℝ)≤alpha) (hC : 0<Ccap) (he : 0<epsilon) :
    ∃ eta : ℝ, 0<eta ∧ eta≤epsilon/2 ∧ ∃ tau : ℝ, 0<tau ∧ ∃ t : ℕ, ∃ ht : 2≤t,
    ∀ᶠ q : ℕ in atTop,
      ∀ (hq : 1≤q) (N : ℕ)
      (Y : Finset (RootTuple (n+1) k (Fin N))) (a : Fin (n+1)→ℤ)
      (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))) (hu : ∀ o, ‖u o‖=1)
      (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
      (hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
      (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
      (normN : Fin k→ℝ),
    let I := concreteRootAmbient (by omega : 0<n+1) (by omega : 0<k) hq ht Y a b u hu hsep hinc hne alpha hp hp1
    ∀ H : ActualBufferedArchive k ((n+1)+1) (((4*k+3)*(n+1))*q) q ⌊tau*(q:ℝ)⌋₊ t
      (RootTuple (n+1) k (Fin N)) (Fin (n+1)→ℤ) (Fin N) normN I 1 1 m,
    (∀j, 0<normN j) → (∀j, normN j≤N) →
    (∀j, (I.W.count j:ℝ)≤normN j) → ∀ mu : ℝ, 0 < mu →
    (∀q∈I.cubes, mu^k≤(ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
    (∀q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ)≤Ccap*mu^k) →
    ∀ w : ℝ, (∀j, w≤Real.log (normN j*I.δ^n)) →
    H.loss≤(2:ℝ)^(eta*(q:ℝ)/2) ∧
    (∀R∈H.countLedger, H.loss*R.upper≤(2:ℝ)^(eta*(q:ℝ))) ∧
    ∃ (r : ℕ) (_hr : r≤H.drops), r ≤ m ∧
      (m:ℝ)*(m+1)/(2*(n+1))*
        Real.log ((((I.cubes.card:ℝ)*mu*I.δ)/(∏j, normN j)^(1/(k:ℝ)))/I.δ)+
      (1/2-((n+1:ℝ)-m)*((n+1:ℝ)-m-1)/(2*(n+1)*(n:ℝ)))*(w-((n+1:ℝ)+m+2)*(epsilon*(q:ℝ)*Real.log 2)) ≤
        degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1)) := by
  classical
  obtain ⟨Kpack,hKpack,hpacking⟩ := projective_direction_count_sharp n
  obtain ⟨eta,heta,hetale,tau,htau,t,ht,henv⟩ :=
    exists_actual_uniform_stopping_error (n+1) k ((n+1)+1) ((4*k+3)*(n+1)) 0 (by omega) he
  obtain ⟨K,hK,Bgrid,Bshort,hB,hBs,hstop⟩ := concrete_stopped_degree_optimization n k t m hk hn ht
  let C0 : ℝ := Bgrid*Ccap^(alpha-1/(k:ℝ))
  let Cs : ℝ := Bshort*Ccap^(alpha-1/(k:ℝ))*(8*max 1 (archiveRadiusCalendar ((n+1)+1) 1 m))
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  have hCs : 0<Cs := by dsimp [Cs]; have := le_max_left (1:ℝ) (archiveRadiusCalendar ((n+1)+1) 1 m); positivity
  refine ⟨eta,heta,hetale,tau,htau,t,ht,?_⟩
  filter_upwards [henv K C0 Cs (Real.log Kpack) hC0 hCs] with q henv
  intro hq N Y a b u hu hsep hinc hne normN
  dsimp only
  intro H hN hNbound hcount mu hmu rlo rhi w hw
  let I := concreteRootAmbient (by omega : 0<n+1) (by omega : 0<k) hq ht Y a b u hu hsep hinc hne alpha hp hp1
  have hbound := henv _ _ _ _ _ _ _ _ _ _ normN I H rfl rfl (fun _ _ => rfl)
    le_rfl le_rfl le_rfl (by omega)
  obtain ⟨hloss,hprod,hlong,hshort,hfloor,hpack⟩ := hbound
  refine ⟨hloss,fun R hR => (hprod R hR).2,?_⟩
  have hd : 0<I.δ := I.width_pos
  have hd1 : I.δ≤1 := by
    change ((2:ℝ)^q)⁻¹≤1
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hpop := hpacking I.δ hd hd1 N u hu hsep
  have hscale : (N:ℝ)*I.δ^n≤Kpack := by
    rw [show (1-(n+1:ℝ))=-(n:ℝ) by ring, Real.rpow_neg hd.le,Real.rpow_natCast] at hpop
    have hh := mul_le_mul_of_nonneg_right hpop (pow_nonneg hd.le n)
    simpa only [mul_assoc,inv_mul_cancel₀ (pow_pos hd n).ne',mul_one] using hh
  have hwpack : w≤Real.log Kpack := by
    let j : Fin k := ⟨0,by omega⟩
    have hj : normN j*I.δ^n≤Kpack :=
      (mul_le_mul_of_nonneg_right (hNbound j) (pow_nonneg hd.le n)).trans hscale
    exact (hw j).trans (Real.log_le_log (mul_pos (hN j) (pow_pos hd n)) hj)
  exact hstop q hq N Y a b u hu hsep hinc hne alpha hp hp1 ⌊tau*(q:ℝ)⌋₊ normN 1 H
    hN (by norm_num) (by simpa using hcount) hα mu Ccap hmu hC rlo rhi
    (epsilon*(q:ℝ)*Real.log 2) w (by have := Real.log_pos (by norm_num : (1:ℝ)<2); positivity)
    hw (hwpack.trans hpack) hlong
    (fun r hr => by convert hshort r hr using 1; congr 1; dsimp [Cs]; ring) hfloor

end KakeyaTwoScale
#print axioms KakeyaTwoScale.eventually_concrete_stopped_optimization
