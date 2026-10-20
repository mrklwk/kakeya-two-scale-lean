module
public import KakeyaTwoScale.ConcreteLongDegreeConstraint
public import KakeyaTwoScale.ActualShortPrefixConstraint
public import KakeyaTwoScale.ActualStoppingCases
public import KakeyaTwoScale.StoppedDegreeOptimization

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

theorem concrete_stopped_degree_optimization (n k t m : ℕ) (hk : 2≤k) (hn : n+1=m+k) (ht : 2≤t) :
    ∃ K : ℝ, 0<K ∧ ∃ Bgrid Bshort : ℕ, 0<Bgrid ∧ 0<Bshort ∧ ∀ (q : ℕ) (hq : 1≤q) (N : ℕ)
      (Y : Finset (RootTuple (n+1) k (Fin N))) (a : Fin (n+1)→ℤ)
      (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))) (hu : ∀ o, ‖u o‖=1)
      (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
      (hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
      (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
      (alpha : ℝ) (hp : 0<alpha) (hp1 : alpha≤1)
      (drop : ℕ) (normN : Fin k→ℝ) (U : ℝ),
    let I := concreteRootAmbient (by omega : 0<n+1) (by omega : 0<k) hq ht Y a b u hu hsep hinc hne alpha hp hp1
    ∀ H : ActualBufferedArchive k ((n+1)+1) (((4*k+3)*(n+1))*q) q drop t
      (RootTuple (n+1) k (Fin N)) (Fin (n+1)→ℤ) (Fin N) normN I 1 U m,
    (∀j, 0<normN j) → 1≤U → (∀j, (I.W.count j:ℝ)≤U*(normN j*1)) →
    1/(k:ℝ)≤alpha → ∀ (mu Ccap : ℝ), 0 < mu → 0<Ccap →
    (∀q∈I.cubes, mu^k≤(ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
    (∀q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ)≤Ccap*mu^k) →
    ∀ E w : ℝ, 0≤ E →
    (∀j, w≤Real.log (normN j*I.δ^n)) → w≤ E →
    (∀ (r : ℕ) (hr : r≤H.drops),
      Real.log K+(r:ℝ)*Real.log ((Bgrid:ℝ)*Ccap^(alpha-1/(k:ℝ))*(H.loss*(H.entryAt r hr).upper))+
        ∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i)≤ E) →
    (∀ (r : ℕ) (hr : r≤H.drops),
      Real.log ((Bshort:ℝ)*Ccap^(alpha-1/(k:ℝ))*(H.loss*(H.entryAt r hr).upper)*
        (8*max 1 (archiveRadiusCalendar ((n+1)+1) 1 m)))≤ E) →
    Real.log (2*H.loss)≤ E →
    ∃ (r : ℕ) (_hr : r≤H.drops), r ≤ m ∧
      (m:ℝ)*(m+1)/(2*(n+1))*
        Real.log ((((I.cubes.card:ℝ)*mu*I.δ)/(∏j, normN j)^(1/(k:ℝ)))/I.δ)+
      (1/2-((n+1:ℝ)-m)*((n+1:ℝ)-m-1)/(2*(n+1)*(n:ℝ)))*(w-((n+1:ℝ)+m+2)*E) ≤
        degreeObjectiveLog m r (fun i => Real.log (H.stageDegrees[i]?.getD 1)) := by
  classical
  obtain ⟨K,hK,Bgrid,hB,hlong⟩ := concrete_archive_long_degree_constraint n k t m (by omega) ht
  obtain ⟨Bshort,hBs,hshort⟩ := ActualBufferedArchive.exists_short_prefix_log_constraint (n+1)
  refine ⟨K,hK,Bgrid,Bshort,hB,hBs,?_⟩
  intro q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN U
  dsimp only
  intro H hN hU hcount hα mu Ccap hmu hC rlo rhi E w hE hw hpack herr hserr hfloor
  let I := concreteRootAmbient (by omega : 0<n+1) (by omega : 0<k) hq ht Y a b u hu hsep hinc hne alpha hp hp1
  let Cstar : ℝ := 8*max 1 (archiveRadiusCalendar ((n+1)+1) 1 m)
  have hstar : 1≤Cstar := by dsimp [Cstar]; have := le_max_left (1:ℝ) (archiveRadiusCalendar ((n+1)+1) 1 m); linarith
  obtain ⟨r,hr,hstop,hbefore,_,_,_⟩ := H.exists_exhaustive_stopping_cases Cstar
    (by have := I.width_pos; nlinarith)
  have hrm : r ≤ m := hr.trans H.drops_le
  refine ⟨r,hr,hrm,?_⟩
  let x := Real.log ((((I.cubes.card:ℝ)*mu*I.δ)/(∏j, normN j)^(1/(k:ℝ)))/I.δ)
  have hstep (i : ℕ) (hi : i≤H.drops) (hi0 : 0 < i)
      (hl : ∃j, (∀l, (H.snapshotAt i).state.length I.δ l≤(H.snapshotAt i).state.length I.δ j) ∧
        Cstar*I.δ<(H.snapshotAt i).state.length I.δ j) :
      (i:ℝ)*x+w-E≤degreeConstraintLog (n+1) (fun s => Real.log (H.stageDegrees[s]?.getD 1)) i := by
    obtain ⟨j,hmax,hjl⟩ := hl
    have hc := H.coordinateState_entryAt (n+1) rfl i hi
    rw [H.entryAt_snapshot i hi] at hc
    have hh := hlong q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN U H
      hN hU hcount hα mu Ccap hmu hC rlo rhi i hi hi0 (by have := hi.trans H.drops_le; omega) j
      (by intro l; have h := hmax l; rw [←hc] at h; exact h)
      (by
        have h := hjl.le
        rw [←hc] at h
        change (8*max 1 (archiveRadiusCalendar ((n+1)+1) 1 m))*I.δ ≤
          (H.coordinateState (n+1) rfl (H.polynomialIndex i hi)).length I.δ j at h
        rw [mul_assoc] at h
        exact h)
    have he := herr i hi
    have hpj := hw j
    change (i:ℝ)*x+w-E≤_ 
    change Real.log (normN j*I.δ^n)+(i:ℝ)*x- _ ≤ _ at hh
    linarith
  have hb : ∀ i, 1≤ i → i<r → (i:ℝ)*x+w-E≤degreeConstraintLog (n+1) (fun s => Real.log (H.stageDegrees[s]?.getD 1)) i := by
    intro i hi hir
    exact hstep i (by omega) hi (hbefore i hir)
  have hs : x-E≤degreePrefixLog (fun s => Real.log (H.stageDegrees[s]?.getD 1)) r ∨
      (r=m ∧ (r:ℝ)*x+w-E≤degreeConstraintLog (n+1) (fun s => Real.log (H.stageDegrees[s]?.getD 1)) r) := by
    rcases hstop with hs | ⟨he,hl⟩
    · left
      have hh := hshort H rfl HEq.rfl (by intro y _ z _ hc htube; exact Prod.ext hc htube)
        hα hN hU hcount mu Ccap hmu hC rlo rhi r hr Cstar (by linarith) hs
      have he := hserr r hr
      change x-Real.log ((Bshort:ℝ)*Ccap^(alpha-1/(k:ℝ))*(H.loss*(H.entryAt r hr).upper)*Cstar) ≤ _ at hh
      change Real.log (_*Cstar)≤ E at he
      linarith
    · by_cases hr0 : 0<r
      · exact Or.inr ⟨he,hstep r hr hr0 hl⟩
      · right
        refine ⟨he,?_⟩
        have heq : r=0 := by omega
        simpa [heq,degreeConstraintLog] using sub_nonpos.mpr hpack
  have hh := stopped_degree_optimization (fun s => Real.log (H.stageDegrees[s]?.getD 1))
    (by omega : m+2≤n+1) hrm hE hb hs (by
      intro hr0
      have hf := H.prefix_last_degree_floor r hr hr0
      linarith) hpack
  simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concrete_stopped_degree_optimization
