-- Implementation of Game of Life.

-- Cell states 'cellT' are represented as constructors 'A' and 'D' for alive / dead state respecitlvely.
-- The definition 'mk_gol' builds an instance of Life CA
-- from an initial configuration of cell states.

import cell_automaton utils data.nat.basic 

open utils

namespace gol
 
section gol

open list function

-- (A)live / (D)ead
@[derive decidable_eq]
inductive cellT | A | D

open cellT

def cellT_str : cellT → string
  | A := "X"
  | D := " "

instance cellT_to_str : has_to_string cellT := ⟨cellT_str⟩

instance cellT_repr : has_repr cellT := ⟨cellT_str⟩

instance : has_coe cellT bool := ⟨λx, x = A⟩

instance coe_back : has_coe bool cellT := ⟨λx, if x then A else D⟩

def step (cell : cellT) (alive_neighbours : ℕ) : cellT :=
  if cell then
    if alive_neighbours < 2 then D else
    if bor (alive_neighbours = 2) (alive_neighbours = 3) then A
    else D
  else
    if alive_neighbours = 3 then A
    else D

def gol_step (cell : cellT) (neigh : list cellT) :=
  step cell (count_at_single neigh A)

end gol

open cellT

attribute [reducible]
def gol := cell_automaton cellT

def mk_gol (g : vec_grid₀ cellT) : gol :=
  ⟨g, D, cell_automatons.moore, gol_step, cell_automatons.ext_one⟩

def empty := fgrid₀.mk 2 2 dec_trivial ⟨0, 1⟩ (λx y, D)

def empty_g :=
  vec_grid₀.mk ⟨2, 2, dec_trivial, ⟨[D, D, D, D], rfl⟩⟩ ⟨0, 1⟩ 

def empty_aut : gol := mk_gol empty

def empty_aut_g : gol := mk_gol empty_g

def row := fgrid₀.mk 1 3 dec_trivial ⟨0, 0⟩ (λx y, A)

def row_gol : gol := mk_gol row

def col := vec_grid₀.mk ⟨3, 1, dec_trivial, ⟨[A, A, A], rfl⟩⟩ ⟨1, -1⟩

def col_gol : gol := mk_gol col

def box := fgrid₀.mk 2 2 dec_trivial ⟨0, 1⟩ (λx y, A)

def box_gol : gol := mk_gol box

def dies := vec_grid₀.mk ⟨3, 2, dec_trivial, ⟨[A, D, A, D, D, A], rfl⟩⟩ ⟨0, 1⟩

def dies_gol : gol := mk_gol dies


private lemma col_even {n} (h : n % 2 = 0) {a} {g} 
  (h₂ : a = mk_gol g)
  (h₃ : a = col_gol) : step_n a n = a :=
begin
  unfold step_n,
  rw @periode_cycle _ _ _ _ 2,
    {rw [h, iterate_zero]},
    {rw h₂, subst h₃, rw ← h₂, refl}
end

lemma col_gol_even {n} (h : n % 2 = 0) : step_n col_gol n = col_gol :=
  col_even h rfl rfl

private lemma col_row {n} (h : n % 2 = 1) {a} {g} 
  (h₂ : a = mk_gol g)
  (h₃ : a = col_gol) : step_n a n = row_gol :=
begin
  unfold step_n,
  rw @periode_cycle _ _ _ _ 2,
    {
      rw [
        h, iterate_one, iterate_zero, h₃
      ]; try { by simp [col_gol, row_gol, mk_gol] },
      refl
    },
    {rw h₃, refl}
end

lemma col_row_odd {n} (h : n % 2 = 1) : step_n col_gol n = row_gol :=
  col_row h rfl rfl

open list prod

def find_period (max : ℕ) (a : gol) : option ℕ :=
  let incr_iota := list.reverse $ list.iota max in
  prod.snd <$> list.find ((=tt) ∘ prod.fst) (
    list.zip (list.map ((=a.g) ∘ cell_automaton.g ∘ (step_n a)) incr_iota) incr_iota
  ) 

meta def solve_periodic_gol_n (n : ℕ) : tactic unit :=
  do {
    `(periodic %%a) ← tactic.target,
    t ← tactic.infer_type a,
    aut ← tactic.eval_expr (cell_automaton _) a,
    let val := find_period n aut in do
      v ← val,
      tactic.existsi `(v),
      tactic.split,
      tactic.exact_dec_trivial,
      tactic.reflexivity
  } <|> tactic.fail
        "Unable to discover periodicity. Try to increase the depth of search."

meta def periodic_aut : tactic unit := solve_periodic_gol_n 16

example : periodic col_gol := ⟨2, ⟨dec_trivial, rfl⟩⟩

example : periodic col_gol := by periodic_aut

end gol