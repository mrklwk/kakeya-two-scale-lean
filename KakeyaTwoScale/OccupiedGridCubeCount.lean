module
public import KakeyaTwoScale.TerminalGridCodes

@[expose] public section

open Set Metric
noncomputable section
set_option maxHeartbeats 2000000
namespace KakeyaTwoScale

/-- Actual occupied-cube count from transverse grid faces and the proved
compact algebraic component theorem. The plane bank contains only bounded
integer labels. No occupancy, entropy, or neighborhood-growth bound is assumed. -/
theorem occupied_grid_cubes_card_le {d s D : ℕ}
    (P : Fin s→MvPolynomial (Fin d) ℝ) (hP : ∀ j, (P j).totalDegree≤D)
    (a : EuclideanSpace ℝ (Fin d)) (theta : Fin d→ℝ) (h : ℝ) (hh : 0<h)
    (hgrid : ∀ (J : Finset (Fin d)) (z : Fin d→ℤ) (x : EuclideanSpace ℝ (Fin d)),
      rectangularPolynomialMap P x=0 → x∈coordinateGridPlane a.ofLp theta h z J → s+J.card≤d)
    (R : ℝ) (hR : 0≤R) (A : Finset (Fin d→ℤ))
    (hocc : ∀ k∈A, ∃ x : EuclideanSpace ℝ (Fin d), rectangularPolynomialMap P x=0 ∧
      x∈closedGridFace a.ofLp theta h k (fun _=>none) ∧ x∈closedBall a R)
    (B : Finset ℤ) (hB : B.Nonempty)
    (hbank : ∀ k∈A, ∀ j, k j∈B ∧ k j+1∈B) :
    A.card≤(2^d*B.card^(d-s))*((4*max D 1+5)^d*2^d) := by
  classical
  let Z := {x | rectangularPolynomialMap P x=0}
  have hf (k : A) : ∃ sigma : Fin d→Option Bool, ∃ x : EuclideanSpace ℝ (Fin d),
      x∈Z∩closedGridFace a.ofLp theta h k sigma ∧
      Z∩closedGridFace a.ofLp theta h k sigma ⊆
        openFreeBox (fun j x => x j) (gridFaceFixed sigma)
          (gridLevel a.ofLp theta h k) (fun j => gridLevel a.ofLp theta h k j+h) := by
    obtain ⟨y,hy,hyc,_⟩ := hocc k k.property
    obtain ⟨sigma,⟨x,hx⟩,ht⟩ := exists_terminal_grid_face Z a.ofLp theta h k ⟨y,hy,hyc⟩
    exact ⟨sigma,x,hx,ht⟩
  choose sigma x hx hterminal using hf
  have hdim (k : A) : (gridFaceFixed (sigma k)).card≤d-s := by
    have hp := (hx k).2
    rw [closedGridFace_eq_plane_box] at hp
    have hd := hgrid _ _ (x k) (hx k).1 hp.1
    omega
  have hlabelsB (k : A) (j) (_hj : j∈gridFaceFixed (sigma k)) :
      gridFaceLabels k (sigma k) j∈B := by
    unfold gridFaceLabels
    split_ifs
    · exact (hbank k k.property j).2
    · simpa using (hbank k k.property j).1
  let p : A→GridPlaneBank d (d-s) B := fun k => terminalFacePlane B k (sigma k) (hdim k) (hlabelsB k)
  let Rbig := R+(d+1)*h
  have hRbig : 0≤Rbig := by dsimp [Rbig]; positivity
  let K : GridPlaneBank d (d-s) B→Set (EuclideanSpace ℝ (Fin d)) := fun p =>
    (Z∩coordinateGridPlane a.ofLp theta h p.labels p.1.val) ∩ closedBall a Rbig
  have hcount (p : GridPlaneBank d (d-s) B) :
      (actualSetComponents (K p)).Finite ∧ (actualSetComponents (K p)).ncard≤(4*max D 1+5)^d :=
    coordinate_slice_components_bound P hP a.ofLp theta h p.labels p.1.val a Rbig hRbig
  have hplane (k : A) : coordinateGridPlane a.ofLp theta h (p k).labels (p k).1.val=
      coordinateGridPlane a.ofLp theta h (gridFaceLabels k (sigma k)) (gridFaceFixed (sigma k)) :=
    terminalFacePlane_plane B k (sigma k) (hdim k) (hlabelsB k) a.ofLp theta h
  have hxR (k : A) : x k∈closedBall a Rbig := by
    obtain ⟨y,_,hy,hyR⟩ := hocc k k.property
    exact grid_face_localization a.ofLp theta h hh.le k (sigma k) a R y hy hyR (hx k).2
  have hxK (k : A) : x k∈K (p k) := by
    change x k∈(Z∩coordinateGridPlane a.ofLp theta h (p k).labels (p k).1.val)∩closedBall a Rbig
    rw [hplane k]
    have hp := (hx k).2
    rw [closedGridFace_eq_plane_box] at hp
    exact ⟨⟨(hx k).1,hp.1⟩,hxR k⟩
  let comp (k : A) := connectedComponentIn (K (p k)) (x k)
  have htrap (k : A) : comp k⊆openFreeBox (fun j x => x j) (gridFaceFixed (sigma k))
      (gridLevel a.ofLp theta h k) (fun j => gridLevel a.ofLp theta h k j+h) := by
    have ht := (terminal_grid_face_component Z a.ofLp theta h k (sigma k)
      (hterminal k) a Rbig (x k) (hx k) (hxR k)).2
    change connectedComponentIn ((Z∩coordinateGridPlane a.ofLp theta h (p k).labels (p k).1.val)∩
      closedBall a Rbig) (x k)⊆_
    rw [hplane k]
    exact ht
  have hlabel (k : A) (j) (hj : j∈gridFaceFixed (sigma k)) :
      (p k).labels j=gridFaceLabels k (sigma k) j := by
    exact GridPlaneBank.labels_mem (p k) j hj
  let inst (p : GridPlaneBank d (d-s) B) : Fintype (actualSetComponents (K p)) := (hcount p).1.fintype
  let Target := Σ p : GridPlaneBank d (d-s) B, (actualSetComponents (K p)) × (Fin d→Bool)
  let code : A→Target := fun k => ⟨p k,⟨⟨comp k,x k,hxK k,rfl⟩,
    fun j => decide (sigma k j=some true)⟩⟩
  have hinj : Function.Injective code := by
    intro k l he
    have hp : p k=p l := congrArg Sigma.fst he
    have hc : comp k=comp l := congrArg (fun v : Target => v.2.1.val) he
    have hb : (fun j => decide (sigma k j=some true))=(fun j => decide (sigma l j=some true)) :=
      congrArg (fun v : Target => v.2.2) he
    have hJ : gridFaceFixed (sigma k)=gridFaceFixed (sigma l) := congrArg (fun p => p.1.val) hp
    have hxl : x k∈comp l := hc ▸ mem_connectedComponentIn (hxK k)
    apply Subtype.ext
    apply terminal_grid_cube_recover a.ofLp theta h hh k l (sigma k) (sigma l) hJ _ hb (x k)
      (htrap k (mem_connectedComponentIn (hxK k))) (htrap l hxl)
    intro j hj
    have hj' : j∈gridFaceFixed (sigma l) := hJ ▸ hj
    exact (hlabel k j hj).symm.trans ((congrArg (fun p => p.labels j) hp).trans (hlabel l j hj'))
  have hc := Fintype.card_le_of_injective code hinj
  have htcard : Fintype.card Target≤Fintype.card (GridPlaneBank d (d-s) B)*((4*max D 1+5)^d*2^d) := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _p : GridPlaneBank d (d-s) B, (4*max D 1+5)^d*2^d := by
        apply Finset.sum_le_sum
        intro p _
        simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (by rw [Set.fintypeCard_eq_ncard]; exact (hcount p).2)
      _ = _ := by simp
  have ht := hc.trans (htcard.trans (Nat.mul_le_mul_right _ (gridPlaneBank_card_le d (d-s) B hB)))
  simpa using ht

end KakeyaTwoScale
#print axioms KakeyaTwoScale.occupied_grid_cubes_card_le
