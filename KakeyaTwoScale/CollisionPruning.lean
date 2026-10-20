module
public import KakeyaTwoScale.CircleCollision
public import KakeyaTwoScale.MeasureSelection

@[expose] public section

noncomputable section
namespace KakeyaTwoScale
open Classical MeasureTheory
open scoped BigOperators

def circleCollisionSet (p : ℕ) (x : ℤ) (S : Finset ℤ) : Set (AddCircle (1:ℝ)) :=
  ⋃ y ∈ S.erase x, {θ | circleBin p (x • θ) = circleBin p (y • θ)}

theorem measurableSet_circleCollisionSet (p : ℕ) (x : ℤ) (S : Finset ℤ) :
    MeasurableSet (circleCollisionSet p x S) :=
  MeasurableSet.biUnion (S.erase x).countable_toSet (fun y _ => measurableSet_circleBin_collision p x y)

theorem circleCollisionSet_measure (p : ℕ) (hp : 0 < p) (x : ℤ) (S : Finset ℤ) :
    volume.real (circleCollisionSet p x S) ≤ (S.card:ℝ)* (2/(p:ℝ)) := by
  have h (y : ℤ) (hy : y ∈ S.erase x) :
      volume.real {θ : AddCircle (1:ℝ) | circleBin p (x • θ) = circleBin p (y • θ)} ≤ 2/(p:ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (circleBin_collision_measure p hp x y (Finset.ne_of_mem_erase hy).symm)
    simpa only [Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2/(p:ℝ))] using hh
  calc
    _ ≤ ∑ y ∈ S.erase x, volume.real {θ : AddCircle (1:ℝ) | circleBin p (x • θ) = circleBin p (y • θ)} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ S.erase x, 2/(p:ℝ) := Finset.sum_le_sum h
    _ = ((S.erase x).card:ℝ)*(2/(p:ℝ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) (by positivity)

def integerFiberXs (G : Finset (ℤ × ℤ)) (y : ℤ) : Finset ℤ :=
  (G.filter (fun v => v.2 = y)).image Prod.fst

def goodCircleParameters (p : ℕ) (G : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Set (AddCircle (1:ℝ)) :=
  (circleCollisionSet p v.2 (G.image Prod.snd) ∪ circleCollisionSet p v.1 (integerFiberXs G v.2))ᶜ

/-- Actual averaging retains at least four fifths of the integer pairs at
modulus p ≥ 20 N, when the vertical set and each fiber have at most N elements. -/
theorem exists_dense_circle_pruning (p N : ℕ) (hp : 0 < p) (hpN : 20*N ≤ p)
    (G : Finset (ℤ × ℤ)) (hV : (G.image Prod.snd).card ≤ N)
    (hF : ∀ v ∈ G, (integerFiberXs G v.2).card ≤ N) :
    ∃ θ : AddCircle (1:ℝ),
      (4/5:ℝ)*G.card ≤ ((G.filter (fun v => θ ∈ goodCircleParameters p G v)).card:ℝ) := by
  let : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) :=
    ⟨by rw [AddCircle.measure_univ]; norm_num⟩
  have hm (v : ℤ × ℤ) : MeasurableSet (goodCircleParameters p G v) :=
    ((measurableSet_circleCollisionSet p v.2 _).union (measurableSet_circleCollisionSet p v.1 _)).compl
  have hbound (v) (hv : v ∈ G) : (4/5:ℝ) ≤ volume.real (goodCircleParameters p G v) := by
    have h1 := circleCollisionSet_measure p hp v.2 (G.image Prod.snd)
    have h2 := circleCollisionSet_measure p hp v.1 (integerFiberXs G v.2)
    have hu := measureReal_union_le (μ := (volume : Measure (AddCircle (1:ℝ))))
      (circleCollisionSet p v.2 (G.image Prod.snd)) (circleCollisionSet p v.1 (integerFiberXs G v.2))
    have hvR : ((G.image Prod.snd).card:ℝ) ≤ N := by exact_mod_cast hV
    have hfR : ((integerFiberXs G v.2).card:ℝ) ≤ N := by exact_mod_cast hF v hv
    have hpR : (0:ℝ) < p := by exact_mod_cast hp
    have hpNR : (20:ℝ)*N ≤ p := by exact_mod_cast hpN
    have hquot : (N:ℝ)*(2/(p:ℝ)) ≤ 1/10 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 10)).mpr
      field_simp
      nlinarith
    have h1' := h1.trans (mul_le_mul_of_nonneg_right hvR (by positivity : 0 ≤ 2/(p:ℝ)))
    have h2' := h2.trans (mul_le_mul_of_nonneg_right hfR (by positivity : 0 ≤ 2/(p:ℝ)))
    unfold goodCircleParameters
    rw [measureReal_compl ((measurableSet_circleCollisionSet p v.2 _).union
      (measurableSet_circleCollisionSet p v.1 _)),probReal_univ]
    linarith
  obtain ⟨θ,hθ⟩ := common_parameter_of_measure_lower (volume : Measure (AddCircle (1:ℝ))) G
    (goodCircleParameters p G) (4/5:ℝ) (fun v _ => hm v) hbound
  exact ⟨θ,by simpa only [membershipCount_eq_card] using hθ⟩

/-- Both stages of collision deletion are used: different heights cannot
collide, and within one retained height different intercepts cannot collide. -/
theorem circle_pruning_injective (p : ℕ) (G : Finset (ℤ × ℤ)) (θ : AddCircle (1:ℝ)) :
    Set.InjOn (fun v : ℤ × ℤ => (circleBin p (v.1 • θ),circleBin p (v.2 • θ)))
      (↑(G.filter (fun v => θ ∈ goodCircleParameters p G v)) : Set (ℤ × ℤ)) := by
  intro v hv w hw he
  obtain ⟨hv,hvg⟩ := Finset.mem_filter.mp hv
  obtain ⟨hw,_⟩ := Finset.mem_filter.mp hw
  have hgood : θ ∉ circleCollisionSet p v.2 (G.image Prod.snd) ∪
      circleCollisionSet p v.1 (integerFiberXs G v.2) := hvg
  have hV : v.2 = w.2 := by
    by_contra hn
    apply hgood
    left
    exact Set.mem_iUnion.mpr ⟨w.2,Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr
      ⟨(fun he => hn he.symm),Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩,congrArg Prod.snd he⟩⟩
  apply Prod.ext ?_ hV
  by_contra hn
  apply hgood
  right
  exact Set.mem_iUnion.mpr ⟨w.1,Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr
    ⟨(fun he => hn he.symm),Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,hV.symm⟩,rfl⟩⟩,
      congrArg Prod.fst he⟩⟩

theorem circle_pruning_vertical_eq (p : ℕ) (G : Finset (ℤ × ℤ)) (θ : AddCircle (1:ℝ))
    (v w : ℤ × ℤ) (hv : v ∈ G.filter (fun v => θ ∈ goodCircleParameters p G v)) (hw : w ∈ G) :
    circleBin p (v.2 • θ) = circleBin p (w.2 • θ) ↔ v.2 = w.2 := by
  constructor
  · intro h
    by_contra hn
    have hgood := (Finset.mem_filter.mp hv).2
    apply hgood
    left
    exact Set.mem_iUnion.mpr ⟨w.2,Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr
      ⟨(fun he => hn he.symm),Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩,h⟩⟩
  · intro h
    rw [h]

end KakeyaTwoScale
#print axioms KakeyaTwoScale.measurableSet_circleCollisionSet
#print axioms KakeyaTwoScale.circleCollisionSet_measure
#print axioms KakeyaTwoScale.exists_dense_circle_pruning
#print axioms KakeyaTwoScale.circle_pruning_injective

#print axioms KakeyaTwoScale.circle_pruning_vertical_eq
