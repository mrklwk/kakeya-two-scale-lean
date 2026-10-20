module
public import KakeyaTwoScale.ConcreteArchiveOriginalCount
public import KakeyaTwoScale.ActualPrefixLengthLog

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Actual active lower records, concrete multiplicity, and nested original
count combined. The constant precedes scale, family and archive. -/
theorem concrete_archive_long_count (n k t fuel : ℕ) (hk : 0<k) (ht : 2≤t) :
    ∃ K : ℝ, 0<K ∧ ∀ (q : ℕ) (hq : 1≤q) (N : ℕ)
      (Y : Finset (RootTuple (n+1) k (Fin N))) (a : Fin (n+1)→ℤ)
      (b u : Fin N→EuclideanSpace ℝ (Fin (n+1))) (hu : ∀ o, ‖u o‖=1)
      (hsep : ∀ o p, o≠p → ((2:ℝ)^q)⁻¹≤Real.arccos |inner ℝ (u o) (u p)|)
      (hinc : ∀ y∈Y, ∀ j, (rootGridCube ((2:ℝ)^q)⁻¹ y.1 ∩
        flatCylinder (b (y.2 j)) (u (y.2 j)) 1 ((2:ℝ)^q)⁻¹).Nonempty)
      (hne : (coarseRootTuples Y ((2:ℝ)^q)⁻¹ a).Nonempty)
      (alpha : ℝ) (hp : 0<alpha) (hp1 : alpha≤1)
      (drop : ℕ) (normN : Fin k→ℝ) (P U : ℝ),
    let I := concreteRootAmbient (by omega : 0<n+1) hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
    ∀ H : ActualBufferedArchive k ((n+1)+1) (((4*k+3)*(n+1))*q) q drop t
      (RootTuple (n+1) k (Fin N)) (Fin (n+1)→ℤ) (Fin N) normN I P U fuel,
    ∀ (r : ℕ) (hr : r≤H.drops), 0<r → r≤n+1 →
    let depth := H.polynomialIndex r hr
    let S := H.coordinateState (n+1) rfl depth
    ∀ (family : Fin k),
    (∀ j, S.length I.δ j≤S.length I.δ family) →
    8*(max 1 (archiveRadiusCalendar ((n+1)+1) 1 fuel)*I.δ)≤S.length I.δ family →
    normN family*(H.entryAt r hr).prefixProduct/
        (((H.entryAt r hr).snapshot.state.grains I.cube).card:ℝ) ≤
      K*I.δ^((r:ℤ)-(n:ℤ))/
        ((List.finRange r).map (H.prefixCaptureLengths depth family)).prod := by
  classical
  obtain ⟨K,hK,hcount⟩ := concrete_archive_original_count n k t fuel hk ht
  let M : ℝ := 2*((2*(n+1)+6:ℝ)*k)
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨M*K,mul_pos hM hK,?_⟩
  intro q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN P U
  dsimp only
  intro H r hr hr0 hrn family hmax hlong
  let I := concreteRootAmbient (by omega : 0<n+1) hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
  let depth := H.polynomialIndex r hr
  let S := H.coordinateState (n+1) rfl depth
  have hcoord : BufferedArchiveSnapshot.ofState S=(H.entryAt r hr).snapshot :=
    H.coordinateState_entryAt (n+1) rfl r hr
  have hX : BufferedArchiveSnapshot.ofState S∈H.snapshots := by
    rw [hcoord,H.entryAt_snapshot]
    exact H.snapshotAt_mem r hr
  obtain ⟨hd,hmul⟩ := concrete_archive_grain_multiplicity (by omega : 0<n+1) hk hq ht
    Y a b u hu hsep hinc hne alpha hp hp1 drop fuel normN P U H _ hX
  have he : hd=(rfl : (BufferedArchiveSnapshot.ofState S).dimension=n+1) := Subsingleton.elim _ _
  rw [he] at hmul
  dsimp only [Eq.mp] at hmul
  have hcert := H.coordinateState_certified (n+1) rfl depth
  obtain ⟨y,hy⟩ := hcert.1
  have hactive : 0<S.height family := by
    have hδ := I.width_pos
    have hR := le_max_left (1:ℝ) (archiveRadiusCalendar ((n+1)+1) 1 fuel)
    by_contra hz
    have he : S.height family=0 := by omega
    change 8*(max 1 (archiveRadiusCalendar ((n+1)+1) 1 fuel)*I.δ)≤S.length I.δ family at hlong
    simp only [FrozenGeometryState.length,he,pow_zero,mul_one] at hlong
    nlinarith
  have hlo := H.entryAt_active_lower r hr hr0
  rw [←hcoord] at hlo
  have hg : S.grain (I.cube y)∈S.grains I.cube := Finset.mem_image.mpr ⟨y,hy,rfl⟩
  have hl := hlo _ hg family hactive
  have hm : ((S.grainRecords I.cube (S.grain (I.cube y)) family).card:ℝ)≤
      M*((S.grainRecords I.cube (S.grain (I.cube y)) family).image (S.original family)).card := by
    simpa only [M,Nat.cast_add,Nat.cast_one,I,concreteRootAmbient,BufferedArchiveSnapshot.ofState] using hmul (S.grain (I.cube y)) family hmax
  have ho := hcount q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN P U H
    depth hr0 hrn y hy family hmax hlong
  have hh := hl.trans (hm.trans (mul_le_mul_of_nonneg_left ho hM.le))
  rw [←hcoord]
  dsimp only [depth,ActualBufferedArchive.polynomialIndex] at hh ⊢
  convert hh using 1
  ring

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concrete_archive_long_count
