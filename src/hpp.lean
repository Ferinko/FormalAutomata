-- Implementation of HPP Lattice Gas CA.

-- Cell states 'cellT' are represented as constructors named as possible combinations of
-- of the four directly-connected cardinal directions. 'X' is an empty cell.
-- The definition 'mk_hpp' builds an instance of HPP
-- from an initial configuration of cell states.

import cell_automaton utils data.list.perm

open utils

namespace hpp

section hpp

-- 'X' is empty
-- 'N' 'W' 'E' 'S' and their combinations represent presence (or absence) of
-- a gas molecule heading in the respective direction.
@[derive decidable_eq]
inductive cellT | X | N | W | E | S
                | NW | NE | NS | WS | WE | ES
                | NWE | NWS | NES | WES | NWSE

-- Cardinal directions of HPP cells.
inductive cardinal | CN | CW | CE | CS

open cellT cardinal

def cellT_str : cellT → string 
	| N    := "↑"
	| W    := "←"
	| E    := "→"
	| S    := "↓"
  | NW   := "↖"
  | NE   := "↗"
  | NS   := "↕"
  | WS   := "↙"
  | WE   := "↔"
  | ES   := "↙"
  | NWE  := "⊥"
  | NWS  := "⊣"
  | NES  := "⊢"
  | WES  := "⊤"
  | NWSE := "+"
  | X    := " "

instance cellT_to_str : has_to_string cellT := ⟨cellT_str⟩

instance cellT_repr : has_repr cellT := ⟨cellT_str⟩

attribute [reducible]
def hpp := cell_automaton cellT

def has_cardinal : cellT → cardinal → bool
  | N CN := tt
  | N _  := ff
  | W CW := tt
  | W _  := ff
  | E CE := tt
  | E _  := ff
  | S CS := tt
  | S _  := ff
  | NW CN := tt
  | NW CW := tt
  | NW _  := ff
  | NE CN := tt
  | NE CE := tt
  | NE _  := ff
  | NS CW := tt
  | NS CE := tt
  | NS _  := ff
  | WS CW := tt
  | WS CS := tt
  | WS _  := ff
  | WE CS := tt
  | WE CN := tt
  | WE _  := ff
  | ES CE := tt
  | ES CS := tt
  | ES _  := ff
  | NWE CN := tt
  | NWE CW := tt
  | NWE CE := tt
  | NWE _  := ff
  | NWS CN := tt
  | NWS CW := tt
  | NWS CS := tt
  | NWS _  := ff
  | NES CN := tt
  | NES CE := tt
  | NES CS := tt
  | NES _  := ff
  | WES CW := tt
  | WES CE := tt
  | WES CS := tt
  | WES _  := ff
  | NWSE _ := tt
  | X _ := ff

def collision : cellT → cellT
  | NS := WE
  | WE := NS
  | x  := x

def translation' : bool → bool → bool → bool → cellT
  | tt tt tt tt := NWSE
  | tt tt tt ff := WES
  | tt tt ff tt := NES
  | tt tt ff ff := ES
  | tt ff tt tt := NWS
  | tt ff tt ff := WS
  | tt ff ff tt := NS
  | tt ff ff ff := S
  | ff tt tt tt := NWE
  | ff tt tt ff := WE
  | ff tt ff tt := NE
  | ff tt ff ff := E
  | ff ff tt tt := NW
  | ff ff tt ff := W
  | ff ff ff tt := N
  | ff ff ff ff := X

def translation (neigh : list cellT) : cellT :=
  let north := list.nth neigh 0 in
  let west  := list.nth neigh 1 in
  let east  := list.nth neigh 2 in
  let south := list.nth neigh 3 in
  match north with
    | none     := X
    | (some n) :=
  match west with
    | none     := X
    | (some w) :=
  match east with
    | none     := X
    | (some e) :=   
  match south with
    | none     := X
    | (some s) :=
      translation' (has_cardinal n CS)
                   (has_cardinal w CE)
                   (has_cardinal e CW)
                   (has_cardinal s CN)
  end end end end

lemma translation_eq_translation' {neigh : list cellT}
  (h : list.length neigh = 4) :
  translation neigh =
    let n := list.nth_le neigh 0 $ by simp [h]; exact dec_trivial in
    let w := list.nth_le neigh 1 $ by simp [h]; exact dec_trivial in
    let e := list.nth_le neigh 2 $ by simp [h]; exact dec_trivial in
    let s := list.nth_le neigh 3 $ by simp [h]; exact dec_trivial in
      translation' (has_cardinal n CS)
                   (has_cardinal w CE)
                   (has_cardinal e CW)
                   (has_cardinal s CN) :=
begin
  cases neigh with x₁ xs₁, cases h,
  cases xs₁ with x₂ xs₂, cases h,
  cases xs₂ with x₃ xs₃, cases h,
  cases xs₃ with x₄ xs₄, cases h,
  cases xs₄ with x₅ xs₅, swap 2, cases h,
  unfold translation, simp,
  delta translation, simp
end

def mk_hpp (g : vec_grid₀ cellT) : hpp :=
  ⟨g, X, cell_automatons.neumann, (λ_ neigh, translation neigh), cell_automatons.ext_one⟩

def hpp_g :=
  vec_grid₀.mk
    ⟨11, 11, dec_trivial,
    ⟨[X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, WE, X, X, X, S, X,
      E, X, X, X, E, X, W, X, X, N, N,
      X, X, X, X, X, N, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X,
      X, X, X, X, X, X, X, X, X, X, X], rfl⟩⟩
    ⟨0, 0⟩ 

def simple := mk_hpp hpp_g

end hpp

end hpp