-- Formalization of cellular automata defined over two-dimensional orthogonal geometric lattices.

-- The structure 'cell_automaton' represents a cellular automaton.

-- The function 'step_n a n' represents the 'n'th generation of the CA 'a'.
-- The function 'make_canonical' computes the canonical form of an automaton.

-- Most theorems present are properties related to this functionality.

import grid utils data.vector

open utils

namespace grid

attribute [simp, reducible]
def Q (α : Type*) [grid α] := relative_grid.carrier α

end grid

open grid

section cell_automatons

structure cell_automaton (α : Type) [decidable_eq α] :=
  (g     : vec_grid₀ α)
  (empty : α)
  (neigh : point → list point)
  (f     : α → list α → α)
  (ext   : bounding_box → bounding_box)

end cell_automatons

section cell_automaton_instances

variables {α : Type} [decidable_eq α] [has_to_string α] (a : cell_automaton α)

open grid

def cell_automaton_to_str := grid_str a.g

instance : has_to_string (cell_automaton α) := ⟨cell_automaton_to_str⟩

instance : has_repr (cell_automaton α) := ⟨cell_automaton_to_str⟩

end cell_automaton_instances

section cell_automaton_quot_setoid_eq 

variables {α : Type} [decidable_eq α] (a a₁ a₂ a₃ : cell_automaton α)

end cell_automaton_quot_setoid_eq

namespace cell_automaton

end cell_automaton

namespace cell_automatons

open cell_automaton grid

def neumann : point → list point
  | ⟨x, y⟩ := 
  [            ⟨x, y - 1⟩,
   ⟨x - 1, y⟩,             ⟨x + 1, y⟩,
               ⟨x, y + 1⟩             ]

def moore : point → list point
  | ⟨x, y⟩ :=
  [ ⟨x - 1, y - 1⟩, ⟨x, y - 1⟩, ⟨x + 1, y - 1⟩,
    ⟨x - 1, y    ⟩,             ⟨x + 1, y    ⟩,
    ⟨x - 1, y + 1⟩, ⟨x, y + 1⟩, ⟨x + 1, y + 1⟩ ]


def bounded_neigh {α} [grid α] (g : α)
  (f : point → list point) (p : grid_point g) : list point := f p

instance neigh_gridpoint_coe {α} [grid α] (g : α) :
  has_coe (point → list point)
          (grid_point g → list point) := ⟨bounded_neigh g⟩

def ext_id : bounding_box → bounding_box := id

def ext_one : bounding_box → bounding_box
  | ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩, h⟩ := ⟨⟨x₁ - 1, y₁ - 1⟩, ⟨x₂ + 1, y₂ + 1⟩,
                                ⟨(add_lt_add h.1 dec_trivial),
                                 (add_lt_add h.2 dec_trivial)⟩⟩

end cell_automatons

section cell_automaton_props

variables {α : Type} [decidable_eq α] (a : cell_automaton α)

end cell_automaton_props

section cell_automaton_ops

open function list prod relative_grid

variables variables {α : Type} [decidable_eq α] (a : cell_automaton α)

def asize := size a.g

def bbox_of_caut := bbox_of_grid a.g

theorem caut_eq_iff {a₁ a₂ : cell_automaton α}
  (hempty : a₁.empty = a₂.empty)
  (hneigh : a₁.neigh = a₂.neigh)
  (hf : a₁.f = a₂.f)
  (hext : a₁.ext = a₂.ext) : a₁ = a₂ ↔ a₁.g = a₂.g :=
  ⟨λh, by simp [h], λh, by cases a₁; cases a₂; congr; cc⟩

private lemma pres_nonempty {α β : Type} {f} {filtered : list (α × β)}
  {l : list ℤ}
  (h : ¬empty_list filtered) (h₁ : l = map f ((fst ∘ unzip) filtered)) : 
  ¬empty_list l :=
  by simp [h₁, map_empty_iff_l_empty, unzip_fst_empty_iff_l_empty, h]

def compute_bounds {α : Type} [decidable_eq α]
                   (a : cell_automaton α) : bounding_box :=
  let bounded  := gip_g a.g in
  let mapped   := ℘ a.g in
  let zipped   := zip bounded mapped in
  let filtered := filter (λx, snd x ≠ a.empty) zipped in
  if h : empty_list filtered
  then ⟨gbl a.g, gtr a.g, grid_is_bounding_box⟩ else
  let unzipped := fst ∘ unzip $ filtered in
  let xs       := map point.x unzipped in
  let ys       := map point.y unzipped in
  let min_x    := min_element xs (pres_nonempty h $ by simp) in
  let max_x    := max_element xs (pres_nonempty h $ by simp) in
  let min_y    := min_element ys (pres_nonempty h $ by simp) in 
  let max_y    := max_element ys (pres_nonempty h $ by simp) in
  ⟨⟨min_x, min_y⟩, ⟨max_x + 1, max_y + 1⟩,
  begin
    simp [(↗), min_x, max_x, min_y, max_y];
    split; rw add_comm; exact int.lt_add_one_of_le (min_elem_le_max_elem _ _)
  end⟩

lemma compute_bounds_pres_overlaid
  : overlaid_by (compute_bounds a) ⟨gbl a.g, gtr a.g, grid_is_bounding_box⟩
  :=
begin
  simp [overlaid_by, compute_bounds],
  generalize h₂ : gip_g a.g = indices,
  by_cases h : empty_list (filter (λ (x : point × α), x.snd ≠ a.empty)
                                  (zip indices ℘ (a.g))); simp [h₂, h],
  {exact ⟨⟨le_refl _, le_refl _⟩, ⟨le_refl _, le_refl _⟩⟩},
  {
    split; split,
    {
      apply le_min_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      apply (zunzip_filter_first_irrel rest),
      rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, bbox_of_grid] at h₅,
      exact h₅.2.1
    },    
    { 
      rw [add_comm, ← sub_le_sub_iff_right (1 : ℤ), add_sub_assoc],
      have : 1 - 1 = (0 : ℤ), from dec_trivial, rw this, rw add_zero,
      apply max_le_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      apply (zunzip_filter_first_irrel rest), rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, bbox_of_grid] at h₅,
      simp [gtr],
      rw [add_comm (-1 : ℤ), ← sub_eq_add_neg, int.le_sub_one_iff],
      exact h₅.2.2
    },
    {
      rw [add_comm, ← sub_le_sub_iff_right (1 : ℤ), add_sub_assoc],
      have : 1 - 1 = (0 : ℤ), from dec_trivial, rw [this, add_zero],
      apply max_le_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      apply (zunzip_filter_first_irrel rest),
      rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, bbox_of_grid] at h₅,
      rw int.le_sub_one_iff,
      exact h₅.1.2
    }, 
    {
      apply le_min_elem_of_all _ _ _ (λx, λh₁, _),
      simp at h₁, rcases h₁ with ⟨y₁, rest, h₃⟩, subst h₃,
      simp [expand_gtr, point.x, point.y],
      apply (zunzip_filter_first_irrel rest),
      rw ← h₂, intros y h₄,
      have h₅ := gip_g_in_grid h₄,
      simp [flip, is_in_grid, bbox_of_grid, expand_gtr, point.x] at h₅,
      rcases h₅ with ⟨⟨h₅, h₆⟩, ⟨h₇, h₈⟩⟩,
      linarith
    }
  }
end

lemma compute_bounds_pres_grid :
    uncurry (↗) (points_of_box $ compute_bounds a) :=
begin
  generalize h : compute_bounds a = bounds,
  simp [points_of_box, uncurry, bounds.h]
end

def canonical_grid :=
  compute_bounds a = ⟨gbl a.g, gtr a.g, grid_is_bounding_box⟩

def make_canonical : cell_automaton α :=
  {a with g := ↑(subgrid a.g (compute_bounds a) (compute_bounds_pres_overlaid _))}

def is_canonical := make_canonical a = a

def aut_eq (a₁ a₂ : cell_automaton α) : Prop :=
  (band : bool → bool → bool) (℘(make_canonical a₁).g = ℘(make_canonical a₂).g)
  $ (band : bool → bool → bool)
    ((make_canonical a₁).g.r = (make_canonical a₂).g.r)
    ((make_canonical a₁).g.c = (make_canonical a₂).g.c)

infix ` ~ₐ `:100 := aut_eq

instance decidable_aut_eq {α} [decidable_eq α] {a₁ a₂} :
  decidable (@aut_eq α _ a₁ a₂) := by simp [(~ₐ)]; apply_instance

def ext_aut (a : cell_automaton α) : cell_automaton α :=
  let new_bb := a.ext (grid_bounds a.g) in
  let new_grid :=
    fgrid₀.mk
      (rows_of_box new_bb)
      (cols_of_box new_bb)
      (mul_pos rows_of_box_pos cols_of_box_pos)
      new_bb.p₁
      (λx y, if h : (⟨y, x⟩ : point) ∈ a.g
             then abs_data a.g $ grid_point_of_prod'
                     ((make_bounded h.1), (make_bounded h.2))
             else a.empty) in
  ⟨new_grid, a.empty, a.neigh, a.f, a.ext⟩

def default_if_nex {α : Type*} [grid α] (empty : carrier α)
  (g : α) (p : point) : carrier α :=
  if h : p ∈ g
  then abs_data g (grid_point_of_prod' (in_grid_bounded g p h))
  else empty

def next_gen (a : cell_automaton α) : cell_automaton α :=
  let new_grid := (ext_aut a).g in
  let cells := ℘ new_grid in
  let neighs := map a.neigh (gip_g new_grid) in
  let defaulted := @default_if_nex (vec_grid₀ α) _ a.empty new_grid in
  let neigh_cells := map (list.map defaulted) neighs in
  let new_cells := zip_with a.f cells neigh_cells in
  let grid :=
    @vec_grid₀.mk _
      ⟨grid_rows new_grid, grid_cols new_grid,
       mul_pos rows_of_box_pos cols_of_box_pos,
      ⟨new_cells, by simp [
                       zip_with_len_l,
                       length_generate_eq_size,
                       size,
                       rows_eq_try_sub_bly,
                       cols_eq_trx_sub_blx,
                       length_gip_g,
                       length_gip,
                       grid_is_bounding_box
                     ]
                  ⟩⟩ new_grid.o in
    make_canonical ⟨grid, a.empty, a.neigh, a.f, a.ext⟩

attribute [simp]
lemma next_gen_empty : (next_gen a).empty = a.empty := rfl

attribute [simp]
lemma next_gen_neigh : (next_gen a).neigh = a.neigh := rfl

attribute [simp]
lemma next_gen_f : (next_gen a).f = a.f := rfl

attribute [simp]
lemma next_gen_ext : (next_gen a).ext = a.ext := rfl

attribute [simp]
lemma iterate_next_gen_empty {n} : (iterate next_gen a n).empty = a.empty :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

attribute [simp]
lemma iterate_next_gen_neigh {n} : (iterate next_gen a n).neigh = a.neigh :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

attribute [simp]
lemma iterate_next_gen_f {n} : (iterate next_gen a n).f = a.f :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

attribute [simp]
lemma iterate_next_gen_ext {n} : (iterate next_gen a n).ext = a.ext :=
  by induction n with n ih; simp [iterate_zero, *, iterate_one]

def step_n (n : ℕ) := iterate next_gen a n

def periodic := {n // n ≠ 0 ∧ step_n a n = a}

def count_at_single {α : Type} [decidable_eq α] (neigh : list α) (valid : α) :=
  list.sum ∘ map (λc, if c = valid then 1 else 0) $ neigh

def yield_at_if_in_neigh {α : Type} [decidable_eq α]
  (a : cell_automaton α) (p : point) :=
  if p ∈ a.neigh p
  then some $ @default_if_nex (vec_grid₀ α) _ a.empty a.g p
  else none

def yield_at (p : point) : α := @default_if_nex (vec_grid₀ α) _ a.empty a.g p

def mod_at (p : point) (x : α) (a : cell_automaton α) : cell_automaton α :=
  ⟨modify_at p x a.g, a.empty, a.neigh, a.f, a.ext⟩

def mod_many (l : list (point × α)) (a : cell_automaton α) : cell_automaton α :=
  ⟨modify_many l a.g, a.empty, a.neigh, a.f, a.ext⟩

end cell_automaton_ops

section counting

variables {α : Type} [decidable_eq α] (a : cell_automaton α)

def count (c : α) : ℕ := count_grid a.g c

lemma count_grid_eq_count {x} : count a x = count_grid a.g x := rfl

lemma count_cast_foa (a : vec_grid₀ α) {x} : count_grid ↑a x = count_grid a x :=
  by unfold_coes; simp [count_grid, gen_aof_eq_gen, gen_foa_eq_gen]

lemma count_cast_aof (a : fgrid₀ α) {x} : count_grid ↑a x = count_grid a x :=
  by unfold_coes; simp [count_grid, gen_aof_eq_gen, gen_foa_eq_gen]

lemma yield_at_nonempty {p} {a : cell_automaton α}
  (h : yield_at a p ≠ a.empty) : p ∈ a.g :=
begin
  by_contradiction contra,
  unfold yield_at default_if_nex at h,
  rw dif_neg contra at h,
  contradiction
end

end counting

namespace cardinals

section cardinals

variables {α : Type} [decidable_eq α] (a : cell_automaton α) (p : point)
          (neigh : point → list point)

def neigh_with_NW := ∀p : point, point.mk (p.x - 1) (p.y - 1) ∈ neigh p

def neigh_with_N  := ∀p : point, point.mk p.x       (p.y - 1) ∈ neigh p

def neigh_with_NE := ∀p : point, point.mk (p.x + 1) (p.y - 1) ∈ neigh p

def neigh_with_W  := ∀p : point, point.mk (p.x - 1) p.y       ∈ neigh p

def neigh_with_E  := ∀p : point, point.mk (p.x + 1) p.y       ∈ neigh p

def neigh_with_SW := ∀p : point, point.mk (p.x - 1) (p.y + 1) ∈ neigh p

def neigh_with_S  := ∀p : point, point.mk p.x       (p.y + 1) ∈ neigh p

def neigh_with_SE := ∀p : point, point.mk (p.x + 1) (p.y + 1) ∈ neigh p

open cell_automatons

lemma neumann_N : neigh_with_N neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma neumann_W : neigh_with_W neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma neumann_E : neigh_with_E neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma neumann_S : neigh_with_S neumann :=
  λ⟨x, y⟩, by simp [neumann]

lemma moore_NW : neigh_with_NW moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_N : neigh_with_N moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_NE : neigh_with_NE moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_W : neigh_with_W moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_E : neigh_with_E moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_SW : neigh_with_SW moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_S : neigh_with_S moore :=
  λ⟨x, y⟩, by simp [moore]

lemma moore_SE : neigh_with_SE moore :=
  λ⟨x, y⟩, by simp [moore]

def NW (h : neigh_with_NW a.neigh) := yield_at a ⟨p.x - 1, p.y - 1⟩

def N (h : neigh_with_N a.neigh) := yield_at a ⟨p.x, p.y - 1⟩

def NE (h : neigh_with_NE a.neigh) := yield_at a ⟨p.x + 1, p.y - 1⟩

def W (h : neigh_with_W a.neigh) := yield_at a ⟨p.x - 1, p.y⟩

def E (h : neigh_with_E a.neigh) := yield_at a ⟨p.x + 1, p.y⟩

def SW (h : neigh_with_SW a.neigh) := yield_at a ⟨p.x - 1, p.y + 1⟩

def S (h : neigh_with_S a.neigh) := yield_at a ⟨p.x, p.y + 1⟩

def SE (h : neigh_with_SE a.neigh) := yield_at a ⟨p.x + 1, p.y + 1⟩

end cardinals

end cardinals