module
public import KakeyaTwoScale.TubeChartSelection
public import KakeyaTwoScale.ChartTubeContainment
public import KakeyaTwoScale.GraphDirectionRealization
public import KakeyaTwoScale.RoundedParentWeightedBrush

@[expose] public section

open scoped BigOperators
noncomputable section
namespace KakeyaTwoScale
open Classical

/-- Actual unit segments in every unit direction, including both endpoints. -/
def ContainsUnitSegments {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin (n+1)))) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin (n+1)), ‖u‖=1 → ∃ b,
    ∀ t ∈ Set.Icc (0:ℝ) 1, b+t • u ∈ K

/-- A bounded Kakeya set supplies a common graph chart for any prescribed
finite set of bounded slopes. The finite interval bank and loss precede the
finite family. All graph axes are actual subsegments of K. -/
theorem kakeya_common_graph_interval (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℕ, 0 < B ∧ ∀ (K : Set (EuclideanSpace ℝ (Fin (n+1)))),
    ContainsUnitSegments K → (∀ x ∈ K, ‖x‖ ≤ R) →
    ∀ {J : Type*} (G : Finset J), G.Nonempty →
    ∀ v : J → Fin n → ℝ, (∀ j ∈ G, ‖v j‖ ≤ 1) →
    ∃ S : Finset J, S ⊆ G ∧ S.Nonempty ∧ G.card ≤ B*S.card ∧
    ∃ s : ℝ, ∃ b : J → Fin n → ℝ,
      (∀ j ∈ S, ‖b j‖ ≤ R) ∧
      ∀ j ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1,
        euclideanUnsplit 0 (heightAffine s (tubeChartLength n)
          (t,segmentPoint (b j) (tubeChartLength n • v j) t)) ∈ K := by
  let L := tubeChartLength n
  have hL : 0 < L := tubeChartLength_pos n
  obtain ⟨N,hN,hinterval⟩ := bounded_height_interval R L hR hL
  let codes := Finset.Icc (-(N:ℤ)) (N:ℤ)
  have hcodes : codes.Nonempty := ⟨0,by simp [codes]⟩
  refine ⟨codes.card,hcodes.card_pos,?_⟩
  intro K hK hbound J G hG v hv
  let u := fun j => graphUnitDirection (0:Fin (n+1)) (v j)
  choose a ha using fun j => hK (u j) (graphUnitDirection_norm 0 (v j))
  have hab (j) : ‖a j‖ ≤ R := hbound _ (by simpa using ha j 0 (by simp))
  have hheight (j) (hj : j ∈ G) : 2*L ≤ u j 0 := by
    have hh := graphUnitDirection_height (0:Fin (n+1)) (v j) 1 (by norm_num) (hv j hj)
    dsimp [L,tubeChartLength,u] at *
    convert hh using 1
    field_simp
    ring
  have hchoose (j) (hj : j ∈ G) : ∃ k ∈ codes,
      a j 0 ≤ (k:ℝ)*L ∧ (k+1:ℝ)*L ≤ a j 0+u j 0 := by
    apply hinterval _ _ _ (hheight j hj)
    have hh : |a j 0| ≤ ‖a j‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (a j) 0
    exact hh.trans (hab j)
  let code := fun j => if hj : j ∈ G then (hchoose j hj).choose else (0:ℤ)
  have hcode (j) (hj : j ∈ G) : code j ∈ codes ∧
      a j 0 ≤ (code j:ℝ)*L ∧ (code j+1:ℝ)*L ≤ a j 0+u j 0 := by
    dsimp [code]; rw [dite_eq_left hj]; exact (hchoose j hj).choose_spec
  obtain ⟨k,hk,hmax⟩ := codes.exists_max_image (fun k => (G.filter (fun j => code j=k)).card) hcodes
  let S := G.filter (fun j => code j=k)
  have hcard : G.card ≤ codes.card*S.card := by
    calc
      _ = ∑ k ∈ codes, (G.filter (fun j => code j=k)).card :=
        Finset.card_eq_sum_card_fiberwise (fun j hj => (hcode j hj).1)
      _ ≤ ∑ _k ∈ codes, S.card := Finset.sum_le_sum (fun k hk => hmax k hk)
      _ = _ := by simp
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have := hG.card_pos
    by_contra hh
    have hz : S.card=0 := by omega
    rw [hz,mul_zero] at hcard
    omega
  let s := (k:ℝ)*L
  let b := fun j => chartIntercept 0 (a j) (u j) s
  have haxis (j) (hj : j ∈ S) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      euclideanUnsplit 0 (heightAffine s L (t,segmentPoint (b j) (L • v j) t)) ∈ K := by
    obtain ⟨hj,hjk⟩ := Finset.mem_filter.mp hj
    have hc := (hcode j hj).2
    rw [hjk] at hc
    have hui : 0 < u j 0 := lt_of_lt_of_le (by positivity : 0 < 2*L) (hheight j hj)
    have htau := chart_parameter_mem hui hL.le hc.1 (by dsimp [s]; nlinarith [hc.2]) ht
    have he := chart_axis_identity (0:Fin (n+1)) (a j) (u j) hui.ne' s L t
    rw [show chartSlope 0 (u j)=v j from graphUnitDirection_chart 0 (v j)] at he
    have he' := congrArg (euclideanUnsplit 0) he
    rw [euclideanUnsplit_split] at he'
    exact he' ▸ ha j _ htau
  refine ⟨S,Finset.filter_subset _ _,hSne,hcard,s,b,?_,haxis⟩
  intro j hj
  have hh := hbound _ (haxis j hj 0 (by simp))
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro l
  have hc := PiLp.norm_apply_le
    (euclideanUnsplit 0 (heightAffine s L (0,segmentPoint (b j) (L • v j) 0))) ((0:Fin (n+1)).succAbove l)
  have he := congrFun (congrArg Prod.snd
    (euclideanSplit_unsplit (0:Fin (n+1)) (heightAffine s L (0,segmentPoint (b j) (L • v j) 0)))) l
  change (euclideanUnsplit 0 (heightAffine s L (0,segmentPoint (b j) (L • v j) 0)))
    ((0:Fin (n+1)).succAbove l)=_ at he
  rw [he] at hc
  simpa [heightAffine,segmentPoint] using hc.trans hh

/-- A concrete rectangular bank of directions gives exact fine lattice
slopes after the common height rescaling. No slope-rounding loss occurs. -/
theorem kakeya_lattice_slope_box (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℕ, 0 < B ∧ ∀ (K : Set (EuclideanSpace ℝ (Fin (n+1)))),
    ContainsUnitSegments K → (∀ x ∈ K, ‖x‖ ≤ R) →
    ∀ (d : ℝ), 0 < d → ∀ N : ℕ, d*N ≤ tubeChartLength n →
    ∃ S : Finset (Fin n → Fin (N+1)), S.Nonempty ∧
      (N+1)^n ≤ B*S.card ∧
      ∃ s : ℝ, ∃ b : (Fin n → Fin (N+1)) → Fin n → ℝ,
        (∀ j ∈ S, ‖b j‖ ≤ R) ∧
        ∀ j ∈ S, ∀ t ∈ Set.Icc (0:ℝ) 1,
          euclideanUnsplit 0 (heightAffine s (tubeChartLength n)
            (t,segmentPoint (b j) (fun l => d*(j l:ℝ)) t)) ∈ K := by
  obtain ⟨B,hB,hh⟩ := kakeya_common_graph_interval n R hR
  refine ⟨B,hB,?_⟩
  intro K hK hbound d hd N hN
  let L := tubeChartLength n
  have hL : 0 < L := tubeChartLength_pos n
  let v := fun j : Fin n → Fin (N+1) => fun l => (d/L)*(j l:ℝ)
  have hv (j : Fin n → Fin (N+1)) (_hj : j ∈ (Finset.univ : Finset (Fin n → Fin (N+1)))) : ‖v j‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro l
    have hj : (j l:ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (j l).isLt)
    have hnon : 0 ≤ (d/L)*(j l:ℝ) := by positivity
    rw [Real.norm_eq_abs,abs_of_nonneg hnon]
    apply (show (d/L)*(j l:ℝ) ≤ d*(N:ℝ)/L from ?_).trans
      ((div_le_one hL).mpr hN)
    calc
      _ = d*(j l:ℝ)/L := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj hd.le) hL.le
  obtain ⟨S,hsub,hSne,hcard,s,b,hb,haxis⟩ := hh K hK hbound Finset.univ
    (Finset.univ_nonempty) v hv
  refine ⟨S,hSne,?_,s,b,hb,?_⟩
  · simpa using hcard
  · intro j hj t ht
    have he : L • v j = (fun l => d*(j l:ℝ)) := by
      funext l
      dsimp [v]
      field_simp
    simpa only [← he] using haxis j hj t ht

/-- Encode the extracted family as literal integer base/slope pairs. The
original true intercept remains available for exact K-containment, while
the lattice base is its actual grid rounding. Cardinality is unchanged. -/
theorem encode_lattice_slope_box {n N : ℕ} (S : Finset (Fin n → Fin (N+1)))
    (b : (Fin n → Fin (N+1)) → Fin n → ℝ) (d : ℝ) :
    ∃ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)),
    ∃ original : ((Fin n → ℤ) × (Fin n → ℤ)) → (Fin n → Fin (N+1)),
      G.card=S.card ∧ Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) ∧
      ∀ p ∈ G, original p ∈ S ∧
        latticePoint d p.1=gridRound d (b (original p)) ∧
        latticePoint d p.2=(fun l => d*(original p l:ℝ)) := by
  let f := fun j : Fin n → Fin (N+1) =>
    (gridIndex d (b j),fun l => (j l:ℤ))
  have hf : Function.Injective f := by
    intro j k he
    have he' := congrArg Prod.snd he
    funext l
    apply Fin.ext
    have hh := congrFun he' l
    dsimp [f] at hh
    exact_mod_cast hh
  let original := Function.invFun f
  have ho : Function.LeftInverse original f := Function.leftInverse_invFun hf
  refine ⟨S.image f,original,Finset.card_image_of_injective S hf,?_,?_⟩
  · intro p hp q hq he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hq
    congr 1
    funext l
    apply Fin.ext
    have hh := congrFun he l
    dsimp [f] at hh
    exact_mod_cast hh
  · intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    rw [ho j]
    refine ⟨hj,rfl,?_⟩
    funext l
    simp [f,latticePoint]

/-- Exact floor counting for the prescribed slope bank, uniform in scale. -/
theorem lattice_slope_box_counts (n : ℕ) (L d : ℝ) (hL : 0 < L) (hLone : L ≤ 1)
    (hd : 0 < d) (hdone : d ≤ 1) :
    d*(Nat.floor (L/d):ℝ) ≤ L ∧
    L^n ≤ d^n*((Nat.floor (L/d)+1:ℕ):ℝ)^n ∧
    d^n*((Nat.floor (L/d)+1:ℕ):ℝ)^n ≤ (2:ℝ)^n := by
  have hfloor : (Nat.floor (L/d):ℝ) ≤ L/d := Nat.floor_le (by positivity)
  have hceil : L/d < (Nat.floor (L/d):ℝ)+1 := Nat.lt_floor_add_one (L/d)
  have hlo : d*(Nat.floor (L/d):ℝ) ≤ L := by
    have hh := mul_le_mul_of_nonneg_left hfloor hd.le
    have he : d*(L/d)=L := by field_simp
    rwa [he] at hh
  have hhi : L ≤ d*((Nat.floor (L/d):ℝ)+1) := by
    have hh := mul_lt_mul_of_pos_left hceil hd
    have he : d*(L/d)=L := by field_simp
    rw [he] at hh
    exact hh.le
  refine ⟨hlo,?_,?_⟩
  · rw [← mul_pow]
    apply pow_le_pow_left₀ hL.le
    simpa using hhi
  · rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith

/-- Bounded Kakeya containment constructs the actual integer lattice graph.
Only the bases are rounded. Uniform positive mass, bounded parameters and
exact original subsegment containment are conclusions. -/
theorem kakeya_lattice_extraction (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : Set (EuclideanSpace ℝ (Fin (n+1))),
    ContainsUnitSegments K → (∀ x ∈ K, ‖x‖ ≤ R) →
    ∀ d : ℝ, 0 < d → d ≤ 1 →
    ∃ G : Finset ((Fin n → ℤ) × (Fin n → ℤ)), G.Nonempty ∧
      Set.InjOn Prod.snd (↑G : Set ((Fin n → ℤ) × (Fin n → ℤ))) ∧
      c ≤ d^n*(G.card:ℝ) ∧ d^n*(G.card:ℝ) ≤ (2:ℝ)^n ∧
      ∃ s : ℝ, ∃ b₀ : ((Fin n → ℤ) × (Fin n → ℤ)) → Fin n → ℝ,
        ∀ j ∈ G, ‖b₀ j‖ ≤ R ∧ ‖latticePoint d j.1‖ ≤ R+1 ∧
          ‖latticePoint d j.2‖ ≤ 1 ∧ latticePoint d j.1=gridRound d (b₀ j) ∧
          ∀ t ∈ Set.Icc (0:ℝ) 1,
            euclideanUnsplit 0 (heightAffine s (tubeChartLength n)
              (t,segmentPoint (b₀ j) (latticePoint d j.2) t)) ∈ K := by
  obtain ⟨B,hB,hbox⟩ := kakeya_lattice_slope_box n R hR
  let L := tubeChartLength n
  have hL : 0 < L := tubeChartLength_pos n
  have hLone : L ≤ 1 := tubeChartLength_le_one n
  have hBreal : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨L^n/B,by positivity,?_⟩
  intro K hK hbound d hd hdone
  let N := Nat.floor (L/d)
  obtain ⟨hN,hlo,hhi⟩ := lattice_slope_box_counts n L d hL hLone hd hdone
  obtain ⟨S,hSne,hcard,s,b,hb,haxis⟩ := hbox K hK hbound d hd N hN
  obtain ⟨G,orig,hGcard,hinj,hencode⟩ := encode_lattice_slope_box S b d
  have hGne : G.Nonempty := Finset.card_pos.mp (by rw [hGcard]; exact hSne.card_pos)
  have hcardReal : (((N+1)^n:ℕ):ℝ) ≤ (B:ℝ)*(S.card:ℝ) := by exact_mod_cast hcard
  have hmass : L^n/B ≤ d^n*(G.card:ℝ) := by
    apply (div_le_iff₀ hBreal).mpr
    rw [hGcard]
    have hh := mul_le_mul_of_nonneg_left hcardReal (pow_nonneg hd.le n)
    push_cast at hh
    exact hlo.trans (by simpa [N,mul_assoc,mul_comm,mul_left_comm] using hh)
  have hupper : d^n*(G.card:ℝ) ≤ (2:ℝ)^n := by
    have hs : S.card ≤ (N+1)^n := by simpa using S.card_le_univ
    have hsreal : (S.card:ℝ) ≤ ((N+1:ℕ):ℝ)^n := by exact_mod_cast hs
    rw [hGcard]
    exact (mul_le_mul_of_nonneg_left hsreal (pow_nonneg hd.le n)).trans hhi
  refine ⟨G,hGne,hinj,hmass,hupper,s,fun p => b (orig p),?_⟩
  intro p hp
  obtain ⟨ho,hbase,hslope⟩ := hencode p hp
  have hb' := hb (orig p) ho
  refine ⟨hb',?_,?_,hbase,?_⟩
  · rw [hbase]
    exact gridRound_norm_le _ R d hb' hd hdone
  · rw [hslope]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro l
    have hj : (orig p l:ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (orig p l).isLt)
    have hn : 0 ≤ d*(orig p l:ℝ) := by positivity
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left hj hd.le).trans (hN.trans hLone)
  · intro t ht
    rw [hslope]
    exact haxis (orig p) ho t ht

/-- The source fine scale gives the explicit natural exponential cardinal
bound required by original-capacity level selection. -/
theorem dyadic_lattice_card_bound (n q N : ℕ)
    (h : (dyadicRadius (20*q))^n*(N:ℝ) ≤ (2:ℝ)^n) :
    N ≤ 2^((20*n)*q+n) := by
  have hp : 0 < (2:ℝ)^(20*q) := by positivity
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hp.le n)
  have he : ((2:ℝ)^(20*q))^n*(dyadicRadius (20*q))^n=1 := by
    rw [← mul_pow,dyadicRadius_pow_cancel,one_pow]
  rw [← mul_assoc,he,one_mul] at hh
  have hr : ((2:ℝ)^(20*q))^n*(2:ℝ)^n=(2:ℝ)^((20*n)*q+n) := by
    rw [← pow_mul,← pow_add]
    congr 1
    ring
  rw [hr] at hh
  exact_mod_cast hh

end KakeyaTwoScale
#print axioms KakeyaTwoScale.kakeya_common_graph_interval

#print axioms KakeyaTwoScale.kakeya_lattice_slope_box

#print axioms KakeyaTwoScale.encode_lattice_slope_box

#print axioms KakeyaTwoScale.lattice_slope_box_counts

#print axioms KakeyaTwoScale.kakeya_lattice_extraction

#print axioms KakeyaTwoScale.dyadic_lattice_card_bound
