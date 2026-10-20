module
public import KakeyaTwoScale.ConcreteArchiveLongCount
public import KakeyaTwoScale.ActualLongPrefixConstraint
public import KakeyaTwoScale.ActualArchiveNormalizedLength

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale

/-- Actual positive-long degree constraints with all count and length bounds
derived from the constructed tube archive. Both constants precede q and all
finite data; the complete prefix error remains visible. -/
theorem concrete_archive_long_degree_constraint (n k t fuel : ℕ) (hk : 0<k) (ht : 2≤t) :
    ∃ K : ℝ, 0<K ∧ ∃ Bgrid : ℕ, 0<Bgrid ∧ ∀ (q : ℕ) (hq : 1≤q) (N : ℕ)
      (Y : Finset (RootTuple (n+1) k (Fin N))) (a : Fin (n+1)→ℤ)
      (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))) (hu : ∀ o, ‖u o‖=1)
      (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
      (hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
      (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
      (alpha : ℝ) (hp : 0<alpha) (hp1 : alpha≤1)
      (drop : ℕ) (normN : Fin k→ℝ) (U : ℝ),
    let I := concreteRootAmbient (by omega : 0<n+1) hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
    ∀ H : ActualBufferedArchive k ((n+1)+1) (((4*k+3)*(n+1))*q) q drop t
      (RootTuple (n+1) k (Fin N)) (Fin (n+1)→ℤ) (Fin N) normN I 1 U fuel,
    (∀j, 0<normN j) → 1≤U → (∀j, (I.W.count j:ℝ)≤U*(normN j*1)) →
    1/(k:ℝ)≤alpha → ∀ (mu Ccap : ℝ), 0 < mu → 0<Ccap →
    (∀q∈I.cubes, mu^k≤(ParentLevel.capacity I.W.tuples I.cube q:ℝ)) →
    (∀q∈I.cubes, (ParentLevel.capacity I.W.tuples I.cube q:ℝ)≤Ccap*mu^k) →
    ∀ (r : ℕ) (hr : r≤H.drops), 0<r → r≤n+1 →
    let S := H.coordinateState (n+1) rfl (H.polynomialIndex r hr)
    ∀ (family : Fin k),
    (∀j, S.length I.δ j≤S.length I.δ family) →
    8*(max 1 (archiveRadiusCalendar ((n+1)+1) 1 fuel)*I.δ)≤S.length I.δ family →
    Real.log (normN family*I.δ^n)+(r:ℝ)*
      Real.log ((((I.cubes.card:ℝ)*mu*I.δ)/(∏j, normN j)^(1/(k:ℝ)))/I.δ)-
      (Real.log K+(r:ℝ)*Real.log ((Bgrid:ℝ)*Ccap^(alpha-1/(k:ℝ))*(H.loss*(H.entryAt r hr).upper))+
        ∑i∈Finset.range r, (i:ℝ)*Real.log (H.upperAt i)) ≤
      degreeConstraintLog (n+1) (fun i => Real.log (H.stageDegrees[i]?.getD 1)) r := by
  classical
  obtain ⟨K,hK,hcount⟩ := concrete_archive_long_count n k t fuel hk ht
  obtain ⟨Bgrid,hB,hmain⟩ := ActualBufferedArchive.exists_archive_joint_band_normalized_length (n+1)
  refine ⟨K,hK,Bgrid,hB,?_⟩
  intro q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN U
  dsimp only
  intro H hN hU hrootcount hα mu Ccap hmu hC rlo rhi r hr hr0 hrn family hmax hlong
  let I := concreteRootAmbient (by omega : 0<n+1) hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
  let S := H.coordinateState (n+1) rfl (H.polynomialIndex r hr)
  have hcoord : BufferedArchiveSnapshot.ofState S=(H.entryAt r hr).snapshot :=
    H.coordinateState_entryAt (n+1) rfl r hr
  have hmax' : ∀j, (H.entryAt r hr).snapshot.state.length I.δ j≤
      (H.entryAt r hr).snapshot.state.length I.δ family := by
    rw [←hcoord]
    exact hmax
  have hlong' : I.δ<(H.entryAt r hr).snapshot.state.length I.δ family := by
    rw [←hcoord]
    change I.δ<S.length I.δ family
    have hd := I.width_pos
    have hR := le_max_left (1:ℝ) (archiveRadiusCalendar ((n+1)+1) 1 fuel)
    change 8*(max 1 (archiveRadiusCalendar ((n+1)+1) 1 fuel)*I.δ)≤S.length I.δ family at hlong
    nlinarith
  have hQ : HEq I.Q (fun z : Fin (n+1)→ℤ =>
      (WithLp.ofLp ⁻¹' gridCell I.δ z : Set (EuclideanSpace ℝ (Fin (n+1))))) := HEq.rfl
  have hinj : ∀y∈I.Y₀, ∀z∈I.Y₀, I.cube y=I.cube z → I.tube y=I.tube z → y=z := by
    intro y _ z _ hc htube
    exact Prod.ext hc htube
  have hgrain : (I.W.grains I.cube).card=1 := by
    change ((concreteRootState Y q a b u).grains Prod.fst).card=1
    rw [concreteRootState_grains Y q a b u hne]
    rfl
  have hlength := (hmain H rfl hQ hinj hα hN (by norm_num) hU hrootcount mu Ccap hmu hC.le rlo rhi
    _ (H.entryAt_mem r hr)).1 _ hmax'
  have hcubes : (0:ℝ)<I.cubes.card := by
    obtain ⟨y,hy⟩ := I.nonempty
    exact_mod_cast Finset.card_pos.mpr ⟨I.cube y,I.support y (I.valid.1 hy)⟩
  have hwidth := I.width_pos
  have hprod : 0<∏j, normN j := Finset.prod_pos (fun j _ => hN j)
  have hLambda : 0<((I.cubes.card:ℝ)*mu*I.δ)/(∏j, normN j)^(1/(k:ℝ)) := by positivity
  have hupper := (H.countLedger_positive (by norm_num : (0:ℝ)<1) hU _ (H.entryAt_mem r hr)).2
  have hE : 0<(Bgrid:ℝ)*Ccap^(alpha-1/(k:ℝ))*(H.loss*(H.entryAt r hr).upper) := by
    have := H.loss_pos
    have : 0<(H.entryAt r hr).upper := by linarith
    positivity
  exact H.entryAt_degree_constraint_of_count_and_length hN hU hrootcount hgrain r hr hrn family hlong'
    hLambda hE hK
    (hcount q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN 1 U H r hr hr0 hrn family hmax hlong)
    hlength

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concrete_archive_long_degree_constraint
