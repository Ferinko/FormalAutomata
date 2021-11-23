-- Implementation of Wireworld.

-- Cell states 'cellT' are represented as follows.
--   'empty'
--   'ehead' for electron head
--   'etail' for electron tail
--   'condu' for conductor
-- The definition 'mk_hpp' builds an instance of HPP
-- from an initial configuration of cell states.

import cell_automaton utils data.vector
open utils

namespace ww

section ww

-- empty | electron head | electron tail | conductor
@[derive decidable_eq]
inductive cellT | empty | ehead | etail | condu

open cellT

def cellT_str : cellT → string 
    | empty := " "
    | ehead := "H"
    | etail := "T"
    | condu := "X"

instance cellT_to_str : has_to_string cellT := ⟨cellT_str⟩

instance cellT_repr : has_repr cellT := ⟨cellT_str⟩

attribute [reducible]
def ww := cell_automaton cellT

def step : cellT → ℕ → cellT
  | empty _ := empty
  | ehead _ := etail
  | etail _ := condu
  | condu c := if c = 1 ∨ c = 2 then ehead else condu

def ww_step (cell : cellT) (neigh : list cellT) :=
      step cell $ count_at_single neigh ehead

def mk_ww (g : vec_grid₀ cellT) : ww :=
    ⟨g, empty, cell_automatons.moore, ww_step, cell_automatons.ext_id⟩

def wire_g :=
  vec_grid₀.mk ⟨1, 5, dec_trivial,
              ⟨[etail, ehead, condu, condu, condu], rfl⟩⟩
                        ⟨0, 1⟩ 

def wire : ww := mk_ww wire_g

def or_g_10 :=
    vec_grid₀.mk ⟨5, 6, dec_trivial,
                        ⟨[etail, ehead, empty, empty, empty, empty,
                          empty, empty, condu, empty, empty, empty,
                            empty, condu, condu, condu, condu, condu,
                            empty, empty, condu, empty, empty, empty,
                            condu, condu, empty, empty, empty, empty], rfl⟩⟩
                        ⟨0, 1⟩

def or_10 : ww := mk_ww or_g_10

def or_g_01 :=
    vec_grid₀.mk ⟨5, 6, dec_trivial,
                        ⟨[condu, condu, empty, empty, empty, empty,
                          empty, empty, condu, empty, empty, empty,
                            empty, condu, condu, condu, condu, condu,
                            empty, empty, condu, empty, empty, empty,
                            etail, ehead, empty, empty, empty, empty], rfl⟩⟩
                        ⟨0, 1⟩

def or_01 : ww := mk_ww or_g_01

open cardinals

section ww_or

def or_gate' :=
    vec_grid₀.mk ⟨5, 6, dec_trivial,
                        ⟨[condu, condu, empty, empty, empty, empty,
                          empty, empty, condu, empty, empty, empty,
                            empty, condu, condu, condu, condu, condu,
                            empty, empty, condu, empty, empty, empty,
                            etail, ehead, empty, empty, empty, empty], rfl⟩⟩
                        ⟨-5, -5⟩

def or_gate : ww := mk_ww or_gate'

def write_input (i₁ : bool) (i₂ : bool) :=
    let (b₁, b₂) := if i₁ then (etail, ehead) else (condu, condu) in
    let (b₃, b₄) := if i₂ then (etail, ehead) else (condu, condu) in
    mod_many
        [(⟨-5, -10⟩, b₁), (⟨-4, -10⟩, b₂), (⟨-5, -6⟩, b₃), (⟨-4, -6⟩, b₄)]
        or_gate

def sim_or (i₁ i₂ : bool) : bool :=
    let sim := step_n (write_input i₁ i₂) 3 in
        yield_at sim ⟨-8, -2⟩ = etail ∧ yield_at sim ⟨-8, -1⟩ = ehead

end ww_or

section ww_xor

inductive direction | N | W | E | S

open direction

structure inout :=
    (p₁ : point)
    (p₂ : point)
    (dir : direction)

structure ww₁ :=
    (aut : ww)
    (ins : list inout)
    (ous : list inout)

def str_of_ww₁ : ww₁ → string
  | ⟨aut, _, _⟩ := to_string aut

instance ww₁_to_str : has_to_string ww₁ := ⟨str_of_ww₁⟩

instance ww₁_repr : has_repr ww₁ := ⟨str_of_ww₁⟩

def mk_ww₁ (g : vec_grid₀ cellT) (inputs outputs : list inout) : ww₁ :=
    ⟨mk_ww g, inputs, outputs⟩

def write (a : ww₁) (n : ℕ) (b : bool) : ww₁ :=
    let input := list.nth a.ins n in
    match input with
        | none := a
        | some ⟨p₁, p₂, dir⟩ :=
            if b then
            match dir with
                | N :=
                    ww₁.mk (mod_many [(up p₁ p₂, ehead), (down p₁ p₂, etail)] a.aut)
                           a.ins a.ous
                | S :=
                    ww₁.mk (mod_many [(down p₁ p₂, ehead), (up p₁ p₂, etail)] a.aut)
                                 a.ins a.ous
                | W :=
                  ww₁.mk (mod_many [(left p₁ p₂, ehead), (right p₁ p₂, etail)] a.aut)
                                 a.ins a.ous
                | E :=
                    ww₁.mk (mod_many [(right p₁ p₂, ehead), (left p₁ p₂, etail)] a.aut)
                                 a.ins a.ous
            end
            else ww₁.mk (mod_many [(p₁, condu), (p₂, condu)] a.aut) a.ins a.ous
    end

def read (a : ww₁) (n : ℕ) : bool :=
    let output := list.nth a.ous n in
    match output with
        | none := ff
        | some ⟨p₁, p₂, dir⟩ :=
        match dir with
            | N := yield_at a.aut (up p₁ p₂) = ehead ∧
                         yield_at a.aut (down p₁ p₂) = etail
            | S := yield_at a.aut (up p₁ p₂) = etail ∧
                         yield_at a.aut (down p₁ p₂) = ehead
            | W := yield_at a.aut (left p₁ p₂) = ehead ∧
                         yield_at a.aut (right p₁ p₂) = etail
            | E := yield_at a.aut (left p₁ p₂) = etail ∧
                         yield_at a.aut (right p₁ p₂) = ehead
        end
    end

def xor_gate' :=
    vec_grid₀.mk ⟨7, 7, dec_trivial,
      ⟨[condu, condu, empty, empty, empty, empty, empty, 
        empty, empty, condu, empty, empty, empty, empty, 
          empty, condu, condu, condu, condu, empty, empty,
          empty, condu, empty, empty, condu, condu, condu,
          empty, condu, condu, condu, condu, empty, empty,
          empty, empty, condu, empty, empty, empty, empty,
          condu, condu, empty, empty, empty, empty, empty], rfl⟩⟩
      ⟨0, 0⟩

def xor_gate_inputs : list inout := [⟨⟨0, 6⟩, ⟨1, 6⟩, E⟩, ⟨⟨0, 0⟩, ⟨1, 0⟩, E⟩]

def xor_gate_outputs : list inout := [⟨⟨5, 3⟩, ⟨6, 3⟩, E⟩]

def mk_xor (a : ww) : ww₁ := ⟨a, xor_gate_inputs, xor_gate_outputs⟩

def xor_gate_w : ww := mk_ww xor_gate'

def xor_gate : ww₁ := mk_xor xor_gate_w

def xor' (b₁ b₂ : bool) : bool :=
    read (mk_xor (step_n (write (write xor_gate 0 b₂) 1 b₁).aut 5)) 0

theorem xor_iff_xor' {b₁ b₂} : bxor b₁ b₂ ↔ xor' b₁ b₂ :=
begin
  cases b₁; cases b₂; split; intros h,
  {
    dsimp at h, contradiction
  },
  {
    have : xor' ff ff = ff, from dec_trivial,
    rw this at h,
    contradiction
  },
  {
    exact dec_trivial
  },
  {
    dsimp, unfold_coes
  },
  {
    exact dec_trivial
  },
  {
    dsimp, unfold_coes
  },
  {
    dsimp at h, contradiction
  },
  {
    have : xor' tt tt = ff, from dec_trivial,
    rw this at h,
    contradiction
  }
end

end ww_xor

end ww

end ww