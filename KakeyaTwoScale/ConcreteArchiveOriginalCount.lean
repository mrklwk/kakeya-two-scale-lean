module
public import KakeyaTwoScale.ActualGrainCountExponent
public import KakeyaTwoScale.ConcreteArchiveMultiplicity

@[expose] public section

open Set Metric MeasureTheory
noncomputable section
namespace KakeyaTwoScale

/-- Concrete source-incidence archives satisfy the precise multiscale bound
for distinct originals of a maximal family in a genuinely long positive grain.
The constant precedes dyadic precision, population and every archive choice. -/
theorem concrete_archive_original_count (n k t fuel : ℕ) (hk : 0<k) (ht : 2≤t) :
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
    ∀ (depth : Fin H.polynomialSnapshots.length), 0<depth.val → depth.val≤n+1 →
    let S := H.coordinateState (n+1) rfl depth
    ∀ y∈S.tuples, ∀ (family : Fin k),
    (∀ j, S.length I.δ j≤S.length I.δ family) →
    8*(max 1 (archiveRadiusCalendar ((n+1)+1) 1 fuel)*I.δ)≤S.length I.δ family →
    let F := (S.grainRecords I.cube (S.grain (I.cube y)) family).image (S.original family)
    let L := H.prefixCaptureLengths depth family
    (F.card:ℝ)≤K*I.δ^((depth.val:ℤ)-(n:ℤ))/((List.finRange depth.val).map L).prod := by
  let C0 : ℝ := (2*(n+1)+6:ℝ)*k
  have hC0 : 0≤C0 := by dsimp [C0]; positivity
  obtain ⟨K,hK,hcount⟩ := actual_grain_original_count_exponent n t 0 fuel ((n+1)+1) 1 C0
    (by norm_num) hC0
  refine ⟨K,hK,?_⟩
  intro q hq N Y a b u hu hsep hinc hne alpha hp hp1 drop normN P U
  dsimp only
  intro H depth hdpos hd y hy family hmax hlong
  let I := concreteRootAmbient (by omega : 0<n+1) hk hq ht Y a b u hu hsep hinc hne alpha hp hp1
  let S := H.coordinateState (n+1) rfl depth
  have hroot := concreteRoot_radius_controlled Y q a b u hk
  have hradius := H.coordinateState_radius_controlled (n+1) rfl depth hroot
  have hrad := S.maximal_family_radius ((n+1)+1) I.δ hradius family hmax
  have hrad' : S.ballRadius≤C0*S.length I.δ family := by
    convert hrad using 1
    dsimp [C0]
    push_cast
    ring
  apply hcount k (((4*k+3)*(n+1))*q) q drop 0 ((n+1)*t)
    (RootTuple (n+1) k (Fin N)) (Fin (n+1)→ℤ) (Fin N) normN I P U H
    (by omega) rfl (fun _ _ => rfl) (by rfl)
    (fun j => le_of_eq (concreteRootState_length Y q a b u j)) u
    (fun _ _ _ => rfl) _ depth hdpos hd y hy family hlong hrad'
  intro o p hop
  exact projective_separation_half_chord (u o) (u p) (hu o) (hu p) _ (hsep o p hop)

end KakeyaTwoScale
#print axioms KakeyaTwoScale.concrete_archive_original_count
