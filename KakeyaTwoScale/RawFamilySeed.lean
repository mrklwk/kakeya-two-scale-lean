module
public import KakeyaTwoScale.FrozenExactSeed
public import KakeyaTwoScale.FrozenStateBalance
public import KakeyaTwoScale.TupleLengthSelection

@[expose] public section

open Set Metric
open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
attribute [local instance] Classical.propDecidable

/-- Simultaneous seed construction from actual variable-length physical
records, not an assumed geometric state or seed. Cube ownership and the
physical records' origins are primitive data; a raw split tree must produce
them. Length selection, exact cutting, localization and balancing are built. -/
theorem exists_seed_from_physical_family {n k A J B : ℕ} {T C O P G : Type}
    [DecidableEq T] [DecidableEq C] (hk : 0 < k)
    (Y : Finset T) (cube : T → C) (tube : T → Fin k → O)
    (Q : C → Set (EuclideanSpace ℝ (Fin n))) (cubes : Finset C)
    (center : C → EuclideanSpace ℝ (Fin n))
    (parent : T → Fin k → P) (grain : C → G) (origin : Fin k → P → G)
    (original : Fin k → P → O) (b u : Fin k → P → EuclideanSpace ℝ (Fin n))
    (L : Fin k → P → ℝ) {δ p : ℝ}
    (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1) (hne : Y.Nonempty)
    (hcubes : ∀ y ∈ Y, cube y ∈ cubes)
    (hbound : (Y.card:ℝ) ≤ (2:ℝ)^B)
    (hu : ∀ j t, ‖u j t‖=1)
    (horiginal : ∀ y ∈ Y, ∀ j, original j (parent y j)=tube y j)
    (horigin : ∀ y ∈ Y, ∀ j, origin j (parent y j)=grain (cube y))
    (hinc : ∀ y ∈ Y, ∀ j, (Q (cube y) ∩
      flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ).Nonempty)
    (hdis : ∀ j o, PairwiseDisjoint
      {t | t ∈ Y.image (fun y => parent y j) ∧ original j t=o}
      (fun t => flatCylinder (b j t) (u j t) (L j t) δ))
    (hlen : ∀ y ∈ Y, ∀ j, δ ≤ L j (parent y j) ∧ L j (parent y j) ≤ δ*2^J)
    (hQ : ∀ q ∈ cubes, ∀ x ∈ Q q, dist x (center q) ≤ (A:ℝ)*δ) :
    ∃ (V : FrozenGeometryState n k T C O) (lift : V.Grain → G),
      V.Valid Y cube tube Q δ ∧ V.Balanced cube cubes p ∧ V.tuples.Nonempty ∧
      (∀ j, V.height j ≤ J) ∧
      V.ballRadius ≤ (A+n+5:ℝ)*δ*(∑ j, (2:ℝ)^(V.height j)) ∧
      tupleCubeMass Y cube cubes p /
        ((((J+1)^k * (3^k*(2*(A+n+5)+1)^n) * (B+1)^(k+1):ℕ):ℝ)) ≤
        tupleCubeMass V.tuples cube cubes p ∧
      (∀ j, (V.count j:ℝ) ≤ 2*((Y.image (fun y => parent y j)).card:ℝ)) ∧
      (∀ y ∈ V.tuples, lift (V.grain (cube y))=grain (cube y)) ∧
      (∀ y ∈ V.tuples, ∀ j, V.geometry δ j (V.parent y j) ⊆
        flatCylinder (b j (parent y j)) (u j (parent y j)) (L j (parent y j)) δ) ∧
      (∀ y ∈ V.tuples, ∀ j, V.axis j (V.parent y j)=u j (parent y j)) := by
  classical
  obtain ⟨band,Z,hZY,hmass,hband⟩ := exists_joint_length_selection Y cube cubes
    (fun y j => L j (parent y j)) hδ hlen hp hp1
  have hZpos : 0 < tupleCubeMass Z cube cubes p := by
    obtain ⟨y,hy⟩ := hne
    have hh := tuple_mass_one_le Y cube cubes hp.le hy (hcubes y hy)
    exact (div_pos (by linarith) (by positivity)).trans_le hmass
  have hZne : Z.Nonempty := by
    have hh := tuple_mass_le_card Z cube cubes hp hp1
    exact Finset.card_pos.mp (by exact_mod_cast (hZpos.trans_le hh))
  let S : FrozenGeometryState n k T C O := {
    Piece := P, Grain := G, tuples := Z, parent := parent, grain := grain,
    origin := origin, original := original, base := b, axis := u,
    height := fun j => (band j).val, ballCenter := fun _ => 0, ballRadius := 0 }
  have hv : S.VariableValid L Y cube tube Q δ := by
    refine ⟨hZY,hu,?_,?_,?_,?_⟩
    · exact fun y hy j => horiginal y (hZY hy) j
    · exact fun y hy j => horigin y (hZY hy) j
    · exact fun y hy j => hinc y (hZY hy) j
    · intro j o t ht v hv htv
      exact hdis j o ⟨Finset.image_subset_image hZY ht.1,ht.2⟩
        ⟨Finset.image_subset_image hZY hv.1,hv.2⟩ htv
  let r : ℝ := δ * ∑ j, (2:ℝ)^((band j).val)
  have hell (j : Fin k) : 0 < S.length δ j := by
    dsimp [FrozenGeometryState.length,S]
    positivity
  have hle (j : Fin k) : S.length δ j ≤ r := by
    dsimp [FrozenGeometryState.length,S,r]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i : Fin k => (2:ℝ)^((band i).val)) (fun i _ => by positivity) (Finset.mem_univ j)) hδ.le
  let j₀ : Fin k := ⟨0,hk⟩
  have hδell : δ ≤ S.length δ j₀ := by
    dsimp [FrozenGeometryState.length,S]
    have hh : (1:ℝ) ≤ 2^((band j₀).val) := one_le_pow₀ (by norm_num)
    nlinarith
  have hδr : δ ≤ r := hδell.trans (hle j₀)
  have hr : 0 < r := hδ.trans_le hδr
  have hbands : ∀ j, ∀ t ∈ S.records j,
      S.length δ j ≤ L j t ∧ L j t ≤ 2*S.length δ j := by
    intro j t ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
    have hh := hband y hy j
    change δ*2^((band j).val) ≤ _ ∧ _ ≤ 2*(δ*2^((band j).val))
    exact ⟨hh.1, by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc, S] using hh.2.le⟩
  obtain ⟨U,liftU,hUv,hUS,hUH,hUr,hUlift,hUmass,hUcount,_,hUgeom,hUaxis⟩ :=
    S.exists_exact_length_seed L Y cube tube Q cubes center hδ hr hδr hp hp1 hv hZne
      (fun y hy => hcubes y (hZY hy)) hbands
      (fun j => (hle j).trans (by linarith))
      (fun q hq x hx => (hQ q hq x hx).trans
        (mul_le_mul_of_nonneg_left hδr (Nat.cast_nonneg A)))
  have hUne : U.tuples.Nonempty := by
    have huPos := (div_pos hZpos (by positivity)).trans_le hUmass
    have hh := tuple_mass_le_card U.tuples cube cubes hp hp1
    exact Finset.card_pos.mp (by exact_mod_cast (huPos.trans_le hh))
  have hUbound : (U.tuples.card:ℝ) ≤ (2:ℝ)^B := by
    exact (Nat.cast_le.mpr (Finset.card_le_card hUv.1)).trans hbound
  obtain ⟨V,liftV,hVv,hVb,hVne,hVU,hVH,hVr,hVlift,hVmass,hVcount,_,hVgeom,hVaxis⟩ :=
    U.exists_balanced_state Y cube tube Q cubes hp hp1 hUv hUne
      (fun y hy => hcubes y (hUv.1 hy)) hUbound
  refine ⟨V,liftU ∘ liftV,hVv,hVb,hVne,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    rw [hVH,hUH]
    exact Nat.le_of_lt_succ (band j).isLt
  · rw [hVr,hUr,hVH,hUH]
    dsimp [r,S]
    ring_nf
    exact le_refl _
  · have h1 := div_le_div_of_nonneg_right hmass
      (by positivity : (0:ℝ) ≤ ((3^k*(2*(A+n+5)+1)^n:ℕ):ℝ))
    have h2 := div_le_div_of_nonneg_right (h1.trans hUmass)
      (by positivity : (0:ℝ) ≤ (((B+1)^(k+1):ℕ):ℝ))
    have hh := h2.trans hVmass
    simpa only [Nat.cast_mul,div_div] using hh
  · intro j
    have hc : (S.count j:ℝ) ≤ (Y.image (fun y => parent y j)).card := by
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hZY)
    have hvcount : (V.count j:ℝ) ≤ U.count j := Nat.cast_le.mpr (hVcount j)
    exact hvcount.trans ((hUcount j).trans (by nlinarith))
  · intro y hy
    dsimp [Function.comp_def]
    rw [hVlift y hy]
    exact hUlift y (hVU hy)
  · intro y hy j
    rw [hVgeom y hy j]
    exact hUgeom y (hVU hy) j
  · intro y hy j
    rw [hVaxis y hy j]
    exact hUaxis y (hVU hy) j

end KakeyaTwoScale
#print axioms KakeyaTwoScale.exists_seed_from_physical_family
