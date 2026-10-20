module
public import KakeyaTwoScale.CoordinateBoxComponents

@[expose] public section

open Set
noncomputable section
namespace KakeyaTwoScale

def gridLevel {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (k : Fin d→ℤ) (j : Fin d) : ℝ :=
  a j+theta j+k j*h

def gridFaceFixed {d : ℕ} (sigma : Fin d→Option Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun j => sigma j≠none)

def closedGridFace {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ) (k : Fin d→ℤ)
    (sigma : Fin d→Option Bool) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, match sigma j with
    | none => gridLevel a theta h k j≤x j ∧ x j≤gridLevel a theta h k j+h
    | some false => x j=gridLevel a theta h k j
    | some true => x j=gridLevel a theta h k j+h}

@[simp] theorem mem_gridFaceFixed {d : ℕ} (sigma : Fin d→Option Bool) (j : Fin d) :
    j∈gridFaceFixed sigma ↔ sigma j≠none := by simp [gridFaceFixed]

theorem gridFaceFixed_update {d : ℕ} (sigma : Fin d→Option Bool) (j : Fin d)
    (hj : sigma j=none) (b : Bool) :
    gridFaceFixed (Function.update sigma j (some b))=insert j (gridFaceFixed sigma) := by
  ext i
  by_cases hi : i=j
  · subst i; simp [hj]
  · simp [hi]

theorem closedGridFace_update_mem {d : ℕ} (a theta : Fin d→ℝ) (h : ℝ)
    (k : Fin d→ℤ) (sigma : Fin d→Option Bool) (j : Fin d)
    (b : Bool) (x : EuclideanSpace ℝ (Fin d)) (hx : x∈closedGridFace a theta h k sigma)
    (he : x j=gridLevel a theta h k j+(if b then h else 0)) :
    x∈closedGridFace a theta h k (Function.update sigma j (some b)) := by
  intro i
  by_cases hi : i=j
  · subst i
    cases b <;> simpa [Function.update,add_zero] using he
  · simpa only [Function.update_of_ne hi] using hx i

/-- Every occupied closed cube has a face meeting Z whose free-coordinate
boundary misses Z. A finite maximum constructs the face; no supplied cell
partition or component-count certificate is used. -/
theorem exists_terminal_grid_face {d : ℕ} (Z : Set (EuclideanSpace ℝ (Fin d)))
    (a theta : Fin d→ℝ) (h : ℝ) (k : Fin d→ℤ)
    (hZ : (Z∩closedGridFace a theta h k (fun _ => none)).Nonempty) :
    ∃ sigma : Fin d→Option Bool,
      (Z∩closedGridFace a theta h k sigma).Nonempty ∧
      Z∩closedGridFace a theta h k sigma ⊆
        openFreeBox (fun j x => x j) (gridFaceFixed sigma)
          (gridLevel a theta h k) (fun j => gridLevel a theta h k j+h) := by
  classical
  let F : Finset (Fin d→Option Bool) := Finset.univ.filter
    (fun sigma => (Z∩closedGridFace a theta h k sigma).Nonempty)
  have hF : F.Nonempty := ⟨fun _=>none,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hZ⟩⟩
  obtain ⟨sigma,hsigma,hmax⟩ := F.exists_max_image (fun sigma => (gridFaceFixed sigma).card) hF
  refine ⟨sigma,(Finset.mem_filter.mp hsigma).2,?_⟩
  intro x hx j hj
  have hsj : sigma j=none := by simpa using hj
  have hxb : gridLevel a theta h k j≤x j ∧ x j≤gridLevel a theta h k j+h := by
    simpa only [hsj] using hx.2 j
  have hne (b : Bool) : x j≠gridLevel a theta h k j+(if b then h else 0) := by
    intro he
    have hu : Function.update sigma j (some b)∈F :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx.1,
        closedGridFace_update_mem a theta h k sigma j b x hx.2 he⟩
    have hb := hmax _ hu
    rw [gridFaceFixed_update sigma j hsj b,Finset.card_insert_of_notMem hj] at hb
    omega
  exact ⟨lt_of_le_of_ne hxb.1 (by simpa using (hne false).symm),
    lt_of_le_of_ne hxb.2 (by simpa using hne true)⟩

end KakeyaTwoScale
#print axioms KakeyaTwoScale.gridFaceFixed_update
#print axioms KakeyaTwoScale.closedGridFace_update_mem
#print axioms KakeyaTwoScale.exists_terminal_grid_face
