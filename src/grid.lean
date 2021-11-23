-- A formalization of two-dimensional orthogonal geometric lattices, simply called 'grid's.

-- The class 'relative_grid' is an abstract interpretation thereof with relative (0, 0)-based indexing.
-- The class 'grid' is a generalization of 'relative_grid' to arbitrary (x, y)-relative grids.

-- Three concrete instances are available.
-- 'vec_grid' and its absolutely-indexed counterpart 'vec_grid₀' represent
-- a homogeneous vector-based implementation.

-- 'dep_vec_grid' is identical to 'vec_grid' but uses dependent indices
-- for its rows and columns

-- absolutely-indexed 'fgrid₀' represents
-- a function-based implementation.

-- The function 'gip_g' enumerates coordinates of a grid.
-- The function 'generate' turns a grid into a sequence of elements.
-- The function 'abs_data g ⟨x, y⟩' yields the element of g at ⟨x, y⟩.
-- The functions 'row' 'col' 'top' 'bot' 'left' 'right' return the respective slices of a grid.
-- The function 'subgrid' returns a subgrid of a grid.

-- Most theorems present are properties related to this functionality.

import utils
import data.vector data.list data.int.basic tactic.omega data.fin
       tactic.linarith tactic.sanity_check

open utils

section grids

class relative_grid (α : Type*) :=
  (carrier  : Type)
  (rows     : α → ℕ)
  (cols     : α → ℕ)
  (nonempty : Πg, rows g * cols g > 0)
  (contents : Πg, fin (rows g) → fin (cols g) → carrier)

class grid (α : Type*) extends relative_grid α :=
  (bl : α → point)

section grid_defs

variables {α : Type*} [grid α] (g : α)

open grid relative_grid

notation `|`:max x `|`:0 := int.nat_abs x

def size := rows g * cols g

attribute [simp]
lemma size_eq_rows_mul_cols : size g = rows g * cols g := rfl

def tr (bl : point) (r c : ℕ) : point :=
  ⟨bl.x + c, bl.y + r⟩

attribute [simp]
def grid_rows := rows g

attribute [simp]
def grid_cols := cols g

attribute [simp]
def gbl := bl g

def gtr := tr (bl g) (rows g) (cols g)

def tl : point := ⟨(bl g).x, (bl g).y + rows g⟩

def br : point := ⟨(bl g).x + cols g, (bl g).y⟩

lemma expand_gbl : gbl g = bl g := by simp

lemma expand_gtr : gtr g = ⟨(bl g).x + cols g, (bl g).y + rows g⟩ :=
  by simp [gtr, tr]

lemma blx_eq_tlx {g : α} : (bl g).x = (tl g).x := by simp [bl, tl]

lemma brx_eq_trx {g : α} : (br g).x = (gtr g).x := by simp [br, expand_gtr]

lemma bly_eq_bry {g : α} : (bl g).y = (br g).y := by simp [br]

lemma tly_eq_try {g : α} : (tl g).y = (gtr g).y := by simp [expand_gtr, tl]

private lemma linear_bounds {l r : ℤ} {c : ℕ} (h₁ : l < r) (h₂ : r - ↑c ≤ l) :
  |l + ↑c - r| < c :=
begin
  rw [← int.coe_nat_lt, @int.nat_abs_of_nonneg (l + ↑c - r) (by linarith)],
  linarith
end

structure bounding_box := (p₁ : point) (p₂ : point) (h : p₁ ↗ p₂)

def bbox_str : bounding_box → string
  | ⟨p₁, p₂, _⟩ := "<(" ++ to_string p₁ ++ ", " ++ to_string p₂ ++ ")>"

instance : has_to_string bounding_box := ⟨bbox_str⟩

instance : has_repr bounding_box := ⟨bbox_str⟩

def points_of_box (bb : bounding_box) : point × point := ⟨bb.p₁, bb.p₂⟩

def rows_of_box (bb : bounding_box) : ℕ :=
  |bb.p₂.y - bb.p₁.y|
  
def cols_of_box (bb : bounding_box) : ℕ :=
  |bb.p₂.x - bb.p₁.x|

private def data_option (g : α) (x y : ℕ) :=
  if h : y < cols g
  then if h₁ : x < rows g
       then some $ contents g ⟨x, h₁⟩ ⟨y, h⟩
       else none
  else none

end grid_defs

section grid_lemmas

open grid relative_grid function

variables {α : Type*} [grid α] {g : α}

private theorem data_data_option {x y : ℕ}
  (h₁ : y < rows g) (h₂ : x < cols g) :
  some (contents g ⟨y, h₁⟩ ⟨x, h₂⟩) = data_option g y x :=
  by unfold data_option; repeat { rw dif_pos; try { simp [is_bounded, h.2] } };
     simpa

lemma rows_of_box_pos {bb : bounding_box} : rows_of_box bb > 0 :=
let ⟨⟨_, y₁⟩, ⟨_, y₂⟩, h⟩ := bb in
begin
  simp only [rows_of_box, gt_from_lt], simp [grid_bounded_iff] at h,
  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg]; omega
end

lemma cols_of_box_pos {bb : bounding_box} : cols_of_box bb > 0 :=
let ⟨⟨x₁, _⟩, ⟨x₂, _⟩, h⟩ := bb in
begin
  simp only [cols_of_box, gt_from_lt], simp [grid_bounded_iff] at h,
  rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg]; omega
end

lemma rows_pos : 0 < rows g :=
  (gt_and_gt_of_mul_gt (nonempty g)).1

lemma cols_pos : 0 < cols g :=
  (gt_and_gt_of_mul_gt (nonempty g)).2

lemma abs_rows_pos : 0 < |rows g| := rows_pos

lemma abs_cols_pos : 0 < |cols g| := cols_pos

lemma coe_rows_pos : (0 : ℤ) < ↑(rows g) := by simp [rows_pos]

lemma coe_cols_pos {g : α} : (0 : ℤ) < ↑(cols g) := by simp [cols_pos]

lemma idx_div_cols_bounded {n} (h : n < size g) :
  (bl g).y + ↑n / ↑(cols g) < (gtr g).y :=
begin
  simp [expand_gtr, gt_from_lt] at *, norm_cast,
  rw mul_comm at h,
  replace h := nat.div_lt_of_lt_mul h,
  linarith
end

lemma idx_mod_cols_bounded {n : ℕ} :
  (bl g).x + ↑n % ↑(cols g) < (gtr g).x :=
  by simp [expand_gtr]; exact int.mod_lt_of_pos _ coe_cols_pos

lemma grid_is_bounding_box : bl g ↗ gtr g :=
let ⟨h₁, h₂⟩ := gt_and_gt_of_mul_gt (nonempty g) in
  grid_bounded_iff.2 ⟨
    by simpa [expand_gtr],
    by simpa [expand_gtr]
  ⟩

def bbox_of_grid (g : α) : bounding_box :=
  ⟨bl g, gtr g, grid_is_bounding_box⟩

theorem bbox_of_grid_p₁ : (bbox_of_grid g).p₁ = (gbl g) := rfl

theorem bbox_of_grid_p₂ : (bbox_of_grid g).p₂ = (gtr g) := rfl

structure relative_point (g : α) :=
  (x : fin (rows g))
  (y : fin (cols g))

def relative_point_str (g : α) : relative_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "]"

instance : has_to_string (relative_point g) :=
  ⟨relative_point_str g⟩ 

instance : has_repr (relative_point g) :=
  ⟨relative_point_str g⟩ 

structure grid_point (g : α) :=
  (y : bounded (bl g).y (gtr g).y)
  (x : bounded (bl g).x (gtr g).x)

def grid_point_str (g : α) : grid_point g → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "] - "
              ++ to_string (bl g)

instance : has_to_string (grid_point g) := ⟨grid_point_str g⟩

instance : has_repr (grid_point g) := ⟨grid_point_str g⟩

lemma gtry_lt_bly : (bl g).y < (gtr g).y :=
  by simp [expand_gtr, rows_pos]

lemma gblx_lt_gtrx : (gbl g).x < (gtr g).x :=
  expand_gtr g ▸ expand_gbl g ▸ lt_add_of_pos_right _ coe_cols_pos

private lemma grid_rows_eq_try_sub_bly :
  grid_rows g = |(gtr g).y - (bl g).y| :=
  by simp [expand_gtr]

lemma rows_eq_try_sub_bly :
  rows g = |(gtr g).y - (bl g).y| := grid_rows_eq_try_sub_bly

lemma rows_eq_try_sub_bly' :
  ↑(rows g) = (gtr g).y - (bl g).y := by simp [gtr, tr]

private lemma grid_cols_eq_trx_sub_blx 
  : grid_cols g = |((gtr g).x - (bl g).x)| :=
  by simp [expand_gtr]

lemma cols_eq_trx_sub_blx 
  : cols g = |((gtr g).x - (bl g).x)| := grid_cols_eq_trx_sub_blx

def relpoint_of_gpoint {g : α} (p : grid_point g) : relative_point g :=
    ⟨
      ⟨|p.y.1 - (bl g).y|,  
       begin
         rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, ⟨y, ⟨yl, yu⟩⟩⟩, simp,
         have eq₁ : x + -(bl g).y ≥ 0, by linarith,
         have eq₂ : (gtr g).y - (bl g).y ≥ 0, by simp [expand_gtr]; linarith,
         rw [
           ← int.coe_nat_lt_coe_nat_iff, rows_eq_try_sub_bly,
           int.nat_abs_of_nonneg eq₁, int.nat_abs_of_nonneg eq₂
         ],
         linarith
       end
      ⟩,
      ⟨|p.x.1 - (bl g).x|,
       have h : p.x.1 - (tl g).x ≥ 0,
         from le_sub_iff_add_le.2 (by simp [tl, p.x.2.1]),
       ((int.coe_nat_lt_coe_nat_iff _ _).1 $
        (int.nat_abs_of_nonneg h).symm ▸
        begin
          let uby := p.x.2.2,
          simp only [expand_gtr] at uby,
          simp only [tl],
          linarith
        end)
      ⟩ 
    ⟩

def gpoint_of_relpoint {g : α} (p : relative_point g) : grid_point g :=
  ⟨
    ⟨(bl g).y + p.x.1,
      ⟨
        by simp [tl, expand_gtr],
        by rcases p with ⟨⟨_, h⟩, _⟩; simp only [tl, expand_gtr, h]; linarith
      ⟩
    ⟩,
    ⟨(bl g).x + p.y.1,
      ⟨
        by simp [tl],
        by rcases p with ⟨⟨_, _⟩, ⟨_, h⟩⟩; simp only [tl, expand_gtr, h]; linarith
      ⟩
    ⟩
  ⟩

lemma relpoint_gpoint_id {g : α} {p : grid_point g} :
  gpoint_of_relpoint (relpoint_of_gpoint p) = p :=
begin
  rcases p with ⟨⟨x, ⟨hx₁, _⟩⟩, ⟨y, ⟨hy₁, _⟩⟩⟩,
  simp [relpoint_of_gpoint, gpoint_of_relpoint, -sub_eq_add_neg],
  have : x - (bl g).y ≥ 0, by linarith,
  have : y - (bl g).x ≥ 0, by linarith,
  split; rw int.nat_abs_of_nonneg; try { simp }; assumption
end

lemma gpoint_relpoint_id {g : α} {p : relative_point g} :
  relpoint_of_gpoint (gpoint_of_relpoint p) = p :=
  by cases p with x y; simp [gpoint_of_relpoint, relpoint_of_gpoint]

def prod_of_rel_point {g : α} (rp : relative_point g) := (rp.x, rp.y)

def prod_of_grid_point {g : α} (ap : grid_point g) := (ap.x, ap.y)

def grid_point_of_prod {g : α}
  (p : bounded (bl g).x (gtr g).x ×
       bounded (bl g).y (gtr g).y) : grid_point g :=
  ⟨p.snd, p.fst⟩

def grid_point_of_prod' {g : α}
  (p : bounded (bl g).y (gtr g).y ×
       bounded (bl g).x (gtr g).x) : grid_point g :=
  ⟨p.fst, p.snd⟩

-- Cell of 'g' at ⟨x, y⟩ relative to origin.
def abs_data (g : α) (gp : grid_point g) :=
  let rp := relpoint_of_gpoint gp in
    (contents g) rp.x rp.y

lemma try_lt_bly : (gbl g).y < (gtr g).y :=
  (grid_bounded_iff.1 grid_is_bounding_box).2

private lemma bounded_establishes_bounds {a b : ℤ}
  (h : a < b) (x : bounded 0 ( |b - a| )) :
  a ≤ a + ↑x ∧ a + ↑x < b :=
have xpos : ↑x ≥ 0, from positive_bounded _,
have xmax : ↑x < |b - a|, from bounded_lt _,
  ⟨
    by apply le_add_of_nonneg_right; unfold coe,
    begin
      unfold_coes at *,
      rw add_comm,
      rw [← int.coe_nat_lt, int.nat_abs_of_nonneg, lt_sub_iff_add_lt] at xmax,
      exact xmax,
      {
        simp [ge_from_le],
        rw [
          ← sub_eq_add_neg, ← add_le_add_iff_right a,
          zero_add, sub_add_cancel
        ],
        exact int.le_of_lt h,
      }
    end
  ⟩

end grid_lemmas

end grids

section grid_impls

-- Vector-based grid concrete instance.
structure vec_grid (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (contents : vector α (r * c))

-- Absolute vector-based grid concrete instance.
structure vec_grid₀ (α : Type) extends vec_grid α :=
  (o : point)

-- Absolute function-based grid concrete instance.
structure fgrid₀ (α : Type) :=
  (r : ℕ)
  (c : ℕ)
  (h : r * c > 0)
  (o : point)
  (contents : bounded o.y (o.y + r) → bounded o.x (o.x + c) → α)

-- Absolute vector-based grid concrete instance with dependent size.
structure dep_vec_grid (α : Type) (r : ℕ) (c : ℕ) :=
  (h : r * c > 0)
  (contents : vector α (r * c))

end grid_impls

section grid_instances

open relative_grid grid

lemma data_not_empty {α : Type} {g : vec_grid₀ α} : ¬empty_list g.contents.to_list :=
assume contra,
begin
  simp [empty_list] at contra,
  have contra₁ := contra.symm,
  rw [list_empty_iff_len, vector.to_list_length] at contra₁,
  rcases g with ⟨⟨_, _, h,_⟩, _⟩,
  linarith
end

lemma linearize_array {x y r c : ℕ}
  (xb : x < c) (yb : y < r) : y * c + x < r * c :=
have h₁ : y * c < r * c, by apply mul_lt_mul yb; omega,
have h₂ : ∃n, nat.succ y + n = r, from nat_le_dest yb,
let ⟨n, h₂⟩ := h₂ in
  by rw [← h₂, right_distrib, nat.succ_mul, add_assoc]; linarith

def rel_point_to_fin {α : Type} [grid α] {g : α}
  (p : relative_point g) : fin (size g) :=
  ⟨p.x * cols g + p.y, linearize_array p.y.2 p.x.2⟩

def grid_point_to_fin {α : Type} [grid α] {g : α}
  (p : grid_point g) : fin (size g) := rel_point_to_fin (relpoint_of_gpoint p)

lemma expand_grid_point_to_fin {α : Type} [grid α] {g : α}
  (p : grid_point g) : grid_point_to_fin p =
  ⟨|p.y.1 - (bl g).y| * cols g + |p.x.1 - (bl g).x|,
  linearize_array
    begin
      rcases p with ⟨_, ⟨y, ⟨_, yu⟩⟩⟩,
      simp only [tl], rw ← int.coe_nat_lt_coe_nat_iff,
      have : y - (grid.bl g).x ≥ 0, by rw [ge_from_le]; linarith,
      rw int.nat_abs_of_nonneg this,
      simp [expand_gtr] at yu,
      linarith
    end
    begin
      rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, _⟩,
      simp only [tl], rw ← int.coe_nat_lt_coe_nat_iff,
      have : x - (bl g).y ≥ 0, by linarith,
      rw [int.nat_abs_of_nonneg this, rows_eq_try_sub_bly'],
      linarith
    end⟩ :=
  by simp [grid_point_to_fin, relpoint_of_gpoint, rel_point_to_fin]; unfold_coes

instance rg_vec_grid {α : Type} :
  relative_grid (vec_grid α) := {
    carrier  := α,
    rows     := λg, g.r,
    cols     := λg, g.c,
    nonempty := λg, g.h,
    contents :=
    λg y x,
      g.contents.nth ⟨
        y.1 * g.c + x.1,
        linearize_array x.2 y.2
      ⟩    
}

instance rg_vec_grid₀ {α : Type} :
  relative_grid (vec_grid₀ α) := {
    carrier  := α,
    rows     := λg, g.r,
    cols     := λg, g.c,
    nonempty := λg, g.h,
    contents :=
    λg y x,
      g.contents.nth ⟨
        y.1 * g.c + x.1,
        linearize_array x.2 y.2
      ⟩   
}

private lemma absolute_bounds {o : ℤ} {r : ℕ}
                              (x : fin r) : o + ↑x < o + ↑r :=
  by simp; cases x; unfold_coes; simpa

instance rg_fgrid₀ {α : Type} :
  relative_grid (fgrid₀ α) := {
    carrier  := α,
    rows     := λg, g.r,
    cols     := λg, g.c,
    nonempty := λg, g.h,
    contents := λg y x,
      g.contents ⟨g.o.y + y, ⟨by simp, absolute_bounds _⟩⟩
                 ⟨g.o.x + x, ⟨by simp, absolute_bounds _⟩⟩
}

instance ag_vec_agrid₀ {α : Type} :
  grid (vec_grid₀ α) := {
    bl := λg, g.o
  }

instance ag_fgrid₀ {α : Type} :
  grid (fgrid₀ α) := {
    bl := λg, g.o
  }

instance rg_dep_fgrid₀ {α : Type} {r c : ℕ} :
  relative_grid (dep_vec_grid α r c) := {
    carrier  := α,
    rows     := λ_, r,
    cols     := λ_, c,
    nonempty := λg, g.h,
    contents :=
    λg y x,
      g.contents.nth ⟨
        y.1 * c + x.1,
        linearize_array x.2 y.2
      ⟩
}

-- instance ag_dep_vec_grid₀ {α : Type} {r c : ℕ} :
--   grid (dep_vec_grid₀ α r c) := {
--     bl := λg, g.o
--   }

def point_of_grid_point {α : Type*} [grid α] {g : α} : grid_point g → point
  | ⟨b₁, b₂⟩ := ⟨b₂, b₁⟩

instance point_grid_point_coe {α : Type*} [grid α] (g : α) :
  has_coe (grid_point g) point := ⟨point_of_grid_point⟩

end grid_instances

section finite_grid

open list int function

section spec

open grid relative_grid

variables {α : Type} {ag : vec_grid₀ α} {fg : fgrid₀ α}

lemma coe_rows_pos_a : ↑ag.r > (0 : ℤ) :=
  by change ag.r with (rows ag); simp [gt_from_lt, rows_pos]

lemma coe_rows_pos_f : ↑fg.r > (0 : ℤ) :=
  by change fg.r with (rows fg); simp [gt_from_lt, rows_pos]

lemma coe_cols_pos_a : ↑ag.c > (0 : ℤ) :=
  by change ag.c with (cols ag); simp [gt_from_lt, cols_pos]

lemma coe_cols_pos_f : ↑fg.c > (0 : ℤ) :=
  by change fg.c with (cols fg); simp [gt_from_lt, cols_pos]

end spec

variables {α : Type*} [grid α] (g : α)

def grp (a b row : ℤ) : list point :=
  map (uncurry point.mk) $ zip (range_pure a b)
                               (repeat row ( |b - a| ))

private lemma expand_grp {a b r} (h : a < b) :
  grp a b r =
  ⟨a, r⟩ :: grp (a + 1) b r :=
begin
  conv_lhs { simp only [grp] },
  rw range_pure_next h,
  have : |b - a| ≥ 1, from nat_abs_ge_one_of_lt h,
  rw repeat_more this, simp [-sub_eq_add_neg],
  exact ⟨
    by simp [uncurry],
    by simp [grp, -sub_eq_add_neg, abs_minus_plus h]
  ⟩
end

private lemma expand_grp_g {g : α} :
  grp (gbl g).x (gtr g).x (gtr g).y = 
  ⟨(gbl g).x, (gtr g).y⟩ ::
  grp ((gbl g).x + 1) (gtr g).x (gtr g).y :=
begin
  simp only [grp],
  have h : range_pure ((gbl g).x) ((gtr g).x) =
           (gbl g).x ::
           range_pure (((gbl g).x) + 1) ((gtr g).x),
    from range_pure_next (grid_bounded_iff.1 grid_is_bounding_box).1,
  rw h,
  have h₁ : repeat ((gtr g).y)
                   ( |(gtr g).x - (gbl g).x| ) = 
            (gtr g).y :: repeat (gtr g).y ( |(gtr g).x - (gbl g).x| - 1),
    {
      simp only [expand_gbl], apply repeat_more, 
      rw ← cols_eq_trx_sub_blx,
      exact abs_cols_pos
    },
  simp only [map, h₁, zip_cons_cons],
  exact ⟨
    by simp [uncurry],
    by rw abs_minus_plus;
       exact (grid_bounded_iff.1 grid_is_bounding_box).1
  ⟩
end

private lemma grp_empty_iff {a b r} :
  empty_list (grp a b r) ↔ b ≤ a :=
  ⟨
    assume h, begin
      by_cases contra : a < b,
        {rw expand_grp at h, cases h, exact contra},
        {exact le_of_not_lt contra}
    end,
    assume h, begin
      unfold grp,
      have : range_pure a b = [],
        by unfold1 range_pure; exact if_neg (not_lt_of_le h),
      simp [zip_nil_left, empty_list, this]
    end
  ⟩

open function

private lemma grp_bounds {a b row : ℤ} :
  ∀{c : point}, c ∈ grp a b row →
    is_bounded a b c.x ∧ is_bounded row (row + 1) c.y :=
assume c h,
begin
  simp [grp] at h,
  rcases h with ⟨a₁, ⟨b₁, ⟨h₂, h₃⟩⟩⟩,
  have h₄ : a₁ ∈ range_pure a b, from pair_in_zip_l h₂,
  have h₅ : b₁ ∈ repeat row ( |b + -a| ), from pair_in_zip_r h₂,
  rw ← h₃,
  split; split,
    {exact (range_pure_bounded h₄).1},
    {exact (range_pure_bounded h₄).2},
    {simp [repeat_bounded h₅, uncurry]},
    {rw (repeat_bounded h₅), exact lt_add_succ _ _}
end

lemma length_grp {a b : ℤ} (h : a < b) {x : ℤ} :
  length (grp a b x) = |b - a| :=
have h₁ : length (range_pure a b) = |b - a|,
  from range_length_pure (int.le_of_lt h),
  by simp [grp, length_map, length_zip_left, length_repeat, h₁]

def gip (p₁ p₂ : point) : list point :=
  join (map (grp p₁.x p₂.x) (range_pure p₁.y p₂.y))

open relative_grid grid

def gip_g {α : Type*} [grid α] (g : α) := gip (bl g) (gtr g)

private lemma expand_gip {p₁ p₂} (h : p₁ ↗ p₂) : 
  gip p₁ p₂ = ⟨p₁.x, p₁.y⟩ :: grp (p₁.x + 1) p₂.x p₁.y
           ++ gip ⟨p₁.x, p₁.y + 1⟩ p₂ :=
  by simp [
       gip, expand_grp (grid_bounded_iff.1 h).1,
       range_pure_next (grid_bounded_iff.1 h).2
     ]

private lemma expand_row_gip {p₁ p₂} (h : p₁ ↗ p₂) : 
  gip p₁ p₂ = 
  grp p₁.x p₂.x p₁.y ++ gip ⟨p₁.x, p₁.y + 1⟩ p₂ :=
  by simp [gip, range_pure_next (grid_bounded_iff.1 h).2]

private lemma expand_gip_g :
  (gip_g g) = grp (gbl g).x (gtr g).x (gbl g).y
              ++ gip ⟨(gbl g).x, (gbl g).y + 1⟩ ⟨(gtr g).x, ((gtr g).y)⟩ :=
begin
  generalize h : gip ⟨(gbl g).x, (gbl g).y⟩ ⟨(gtr g).x, ((gtr g).y + 1)⟩ = t,
  simp only [gip_g, gip],
  rw range_pure_next, dsimp,
    {apply congr_arg, simp [h.symm, gip]},
    {exact try_lt_bly}
end

def is_in_grid' (xy : point) :=
  is_bounded (gbl g).y (gtr g).y xy.y ∧
  is_bounded (gbl g).x (gtr g).x xy.x

def is_in_grid (bb : bounding_box) (xy : point) :=
  is_bounded bb.p₁.y bb.p₂.y xy.y ∧ is_bounded bb.p₁.x bb.p₂.x xy.x

attribute [reducible]
instance has_mem_grid : has_mem point α := ⟨flip is_in_grid'⟩

attribute [reducible]
instance has_mem_bb : has_mem point bounding_box := ⟨flip is_in_grid⟩

lemma gip_in_grid {p₁ p₂ : point} {h : p₁ ↗ p₂} :
  ∀{a}, a ∈ gip p₁ p₂ → a ∈ (⟨p₁, p₂, h⟩ : bounding_box) :=
assume a h,
begin
  simp [gip] at h,
  cases a with al ar,
  rcases h with ⟨l, ⟨⟨a₁, ⟨h₂, h₃⟩⟩, h₁⟩⟩,
  have h₄ := range_pure_bounded h₂, rw ← h₃ at h₁,
  have h₅ := grp_bounds h₁,
  split; split,
    {
      simp [bounding_box.p₁],
      rcases h₅ with ⟨⟨h₅l₁, h₅l₂⟩, ⟨h₅r₁, h₅r₂⟩⟩,
      cases h₄, transitivity a₁; assumption
    },
    {exact lt_of_le_of_lt (le_of_lt_add_one h₅.2.2) h₄.2},
    {exact h₅.1.1},
    {exact h₅.1.2}
end

lemma gip_g_in_grid {g : α} :
  ∀{a}, a ∈ gip_g g → a ∈ (bbox_of_grid g) :=
  assume a h, gip_in_grid h

private def make_bounded_idx {g : α} {p : point} (h : p ∈ (bbox_of_grid g)) :
  bounded (bl g).x (gtr g).x ×
  bounded (gbl g).y (gtr g).y :=
    (make_bounded h.2, make_bounded h.1)

private def make_bounded_indices (is : list point)
                         (h : ∀p, p ∈ is → p ∈ (bbox_of_grid g)) :
  list (
    bounded (bl g).x (gtr g).x ×
    bounded (gbl g).y (gtr g).y
  ) := map (λp : {x // x ∈ is},
           (⟨p.1.1, (h p.1 p.2).2⟩,
            ⟨p.1.2, (h p.1 p.2).1⟩)) (attach is)

instance decidable_is_in_grid' {xy : point}
   : decidable (is_in_grid' g xy) :=
   by simp [is_in_grid']; apply_instance

instance decidable_is_in_grid (bb : bounding_box) {xy : point}
   : decidable (is_in_grid bb xy) :=
   by simp [is_in_grid]; apply_instance

instance decidable_is_in_grid'_op {xy : point}
   : decidable (xy ∈ g) :=
   by simp [(∈), is_in_grid', flip]; apply_instance

instance decidable_is_in_grid_op (bb : bounding_box) {xy : point}
   : decidable (xy ∈ bb) :=
   by simp [is_in_grid, (∈), flip]; apply_instance

private def inject_into_bounded (p : {x // x ∈ gip_g g}) :
  bounded (bl g).x (gtr g).x ×
  bounded (gbl g).y (gtr g).y :=
  make_bounded_idx (gip_g_in_grid p.2)

private def inject_row_into_bounded
  {a b r} (p : {x // x ∈ grp a b r}) : 
  bounded a b × bounded r (r + 1) :=
  ⟨⟨p.1.1, (grp_bounds p.2).1⟩, ⟨p.1.2, (grp_bounds p.2).2⟩⟩

private lemma blgx_trgx_of_mem {g : α} {x} {y} (h : point.mk x y ∈ g) :
  (bl g).x < (gtr g).x :=
  by simp only [(∈), flip, is_in_grid'] at h; exact lt_of_le_of_lt h.2.1 h.2.2

theorem in_gip_g_of_in_g {α : Type*} [grid α] {g : α} {p}
  (h : p ∈ g) : p ∈ gip_g g :=
begin  
  cases p with x y,
  simp [-gtr, gip_g, gip],
  have h₂ : y ∈ range_pure (gbl g).y (gtr g).y,
    by simp [(∈), flip, is_in_grid'] at h; exact in_range_iff.2 h.1,
  split, {
    split,
      {use y, exact ⟨h₂, by simp [grp]⟩},
      {
        generalize h₂ : range_pure ((bl g).x) ((gtr g).x) = l₁,
        generalize h₃ : repeat y ( |(gtr g).x - (bl g).x| ) = l₂,
        rw point_in_zip_prod_iff,
        apply point_in_zip_repeat_right _ h₃ _,
          {
            simp [
              h₂.symm, h₃.symm, range_length_pure, length_repeat,
              int.le_of_lt (blgx_trgx_of_mem h)
            ]
          },
          {
            rw [← h₂, in_range_iff],
            simp only [(∈), flip, is_in_grid'] at h, 
            exact h.2
          }
      }
    } 
end

theorem in_grid_iff_in_gip_g {p} {g : α} : p ∈ g ↔ p ∈ gip_g g :=
  ⟨
    in_gip_g_of_in_g,
    λh, by apply gip_in_grid h; exact grid_is_bounding_box
  ⟩
  
private def grid_point_of_mem {p} (h : p ∈ g) : grid_point g :=
  ⟨make_bounded h.1, make_bounded h.2⟩

def generate :=
  map (abs_data g ∘ grid_point_of_prod ∘ inject_into_bounded g)
      (attach $ gip_g g)

notation `℘` g:max := generate g

section grid_instances

instance vec_grid_functor : functor vec_grid := {
  map := λα β f g, {g with contents := vector.map f g.contents}
}

instance vec_grid_functor_law : is_lawful_functor vec_grid := {
  id_map := λα ⟨r, c, h, d⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨r, c, h, d⟩, by simp [(<$>)]
}

instance vec_grid₀_functor : functor vec_grid₀ := {
  map := λα β f g, {g with contents := vector.map f g.contents}
}

instance vec_grid₀_functor_law : is_lawful_functor vec_grid₀ := {
  id_map := λα ⟨⟨r, c, h, d⟩, o⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨⟨r, c, h, d⟩, o⟩, by simp [(<$>)]
}

instance fgrid₀_functor : functor fgrid₀ := {
  map := λα β f g, {g with contents := λx y, f (g.contents x y)}
}

instance fgrid₀_functor_law : is_lawful_functor fgrid₀ := {
  id_map := λα ⟨r, c, h, d, o⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨r, c, h, d, o⟩, by simp [(<$>)]
}

instance dep_vec_grid₀_functor {m n} : functor (λt, dep_vec_grid t m n) := {
  map := λα β f g, {g with contents := vector.map f g.contents}
}

instance dep_vec_grid₀_functor_law {m n} :
  is_lawful_functor (λt, dep_vec_grid t m n) := {
  id_map := λα ⟨r, c, h⟩, by simp [(<$>)],
  comp_map := λα β γ f h ⟨r, c, h⟩, by simp [(<$>)]
}

end grid_instances

attribute [simp]
lemma vec_grid_fmap_r {α β : Type} {g : vec_grid α} {f : α → β} : (f <$> g).r = g.r :=
  by simp [(<$>)]

attribute [simp]
lemma vec_grid_fmap_c {α β : Type} {g : vec_grid α} {f : α → β} : (f <$> g).c = g.c :=
  by simp [(<$>)]

attribute [simp]
lemma vec_grid₀_fmap_r {α β : Type} {g : vec_grid₀ α} {f : α → β} : (f <$> g).r = g.r
  := by simp [(<$>)]

attribute [simp]
lemma vec_grid₀_fmap_c {α β : Type} {g : vec_grid₀ α} {f : α → β} : (f <$> g).c = g.c
  := by simp [(<$>)]

attribute [simp]
lemma fgrid₀_fmap_r {α β : Type} {g : fgrid₀ α} {f : α → β} : (f <$> g).r = g.r
  := by simp [(<$>)]

attribute [simp]
lemma fgrid₀_fmap_c {α β : Type} {g : fgrid₀ α} {f : α → β} : (f <$> g).c = g.c
  := by simp [(<$>)]

def point_of_bounded_prod {a b c d : ℤ} : bounded a b × bounded c d → point
  | ⟨⟨a, _⟩, ⟨c, _⟩⟩ := ⟨a, c⟩

lemma gip_g_nonempty : ¬empty_list (gip_g g) :=
assume contra,
begin
  simp [gip_g, gip] at contra,
  have c₁ : ¬empty_list (
    range_pure (bl g).y (gtr g).y
  ),
    {
      simp only [empty_list], intros c₂, symmetry' at c₂,
      rw range_pure_empty_iff at c₂,
      have c₃ := @grid_is_bounding_box _ _ g, rw grid_bounded_iff at c₃,
      exact absurd (lt_of_le_of_lt c₂ c₃.2) (lt_irrefl _)
    },
  have c₂ := @not_map_empty_of_not_empty _ _ _
    (grp (bl g).x (tr (bl g) (rows g) (cols g)).x) c₁,
  have c₃ := not_join_empty_of_not_empty contra,
  cases c₃,
    {contradiction},
    {
      revert c₃ contra c₂ c₁,
      generalize c₆ : bl g = bl,
      generalize c₅ : tr bl (rows g) (cols g) = tr',
      generalize c₄ :
        map (grp bl.x tr'.x) (range_pure bl.y (gtr g).y) = l,
      let h₃ := @grid_is_bounding_box _ _ g, rw grid_bounded_iff at h₃,
      simp [gtr, c₆, c₅] at h₃,
      intros,
      have c₅ : ∃z ∈ l, ¬empty_list z,
        {
          let h := grp bl.x tr'.x bl.y,
          have h₁ : h = grp bl.x tr'.x bl.y, by cc,
          use h, split,
            {
              rw h₁, revert c₄,
              generalize h₂ : range_pure bl.y tr'.y = l₁, intros,
              cases l₁ with w ws,
                {
                  rw range_pure_empty_iff at h₂,
                  exact absurd (lt_of_le_of_lt h₂ h₃.2) (lt_irrefl _)
                },
                {
                  have h₄ : w = bl.y,
                    by unfold1 range_pure at h₂; rw if_pos h₃.2 at h₂;
                       injection h₂ with h₃ _; rw h₃,
                  have : bl.y < (gtr g).y, by subst c₅; simp [gtr, c₆]; exact h₃.2,
                  simp [c₄.symm, range_pure_next this]
                },
            },
            {
              unfold1 grp at h₁,
              have h₂ : tr'.x > bl.x, from h₃.1,
              have h₄ : range_pure (bl.x) (tr'.x) =
                        bl.x :: range_pure (bl.x + 1) (tr'.x),
                from range_pure_next h₂,
              rw h₄ at h₁,
              have : |tr'.x - bl.x| ≥ 1,
                begin
                  apply nat.succ_le_of_lt (lt_of_coe_nat_lt_coe_nat _),
                  rw [nat_abs_of_nonneg, lt_sub],
                  simpa, linarith
                end,
              have h₅ : repeat bl.y ( |tr'.x - bl.x| ) =
                bl.y :: repeat bl.y (( |tr'.x - bl.x| ) - 1),
                from repeat_more this,
              rw [h₅, zip_cons_cons, map_cons] at h₁, rw h₁,
              apply not_empty_cons
            }
        },
      rcases c₅ with ⟨c₅l, ⟨c₅₁, c₅₂⟩⟩, rw [← c₄, ← c₅] at c₅₁,
      simp only [gtr] at c₃, subst c₆,
      exact absurd (c₃ c₅l c₅₁) c₅₂
    } 
end

lemma length_gip {p₁ p₂ : point} (h : p₁ ↗ p₂) :
  length (gip p₁ p₂) = |p₂.y - p₁.y| * |p₂.x - p₁.x| :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← nat_abs_mul],
  rw grid_bounded_iff at h,
  have h₁ : (p₂.y - p₁.y) * (p₂.x - p₁.x) > 0,
    {cases p₁, cases p₂, apply mul_pos; omega},
  simp [
    -sub_eq_add_neg, gip, length_join, (∘), length_grp h.1,
    range_length_pure (int.le_of_lt h.2),
    nat_abs_of_nonneg (int.le_of_lt h₁)
  ],
  repeat {rw nat_abs_of_nonneg}; simp [-sub_eq_add_neg, ge_from_le];
  apply int.le_of_lt; simp [h.1, h.2]
end

theorem length_gip_g : length (gip_g g) = rows g * cols g :=
  by simp [
       gip_g, length_gip, rows_eq_try_sub_bly, cols_eq_trx_sub_blx,
       grid_is_bounding_box
     ]

private theorem length_generate {α : Type*} [grid α] (g : α) :
  length (℘ g) = grid_rows g * grid_cols g :=
by unfold generate gip_g;
   rw [
     length_map, grid_rows_eq_try_sub_bly, grid_cols_eq_trx_sub_blx,
     length_attach, length_gip_g, rows_eq_try_sub_bly, cols_eq_trx_sub_blx
   ]

lemma length_generate_eq_size :
  length (℘ g) = size g := by simp [size, length_generate]

lemma map_generate_map_v₀ {α β : Type} {g : vec_grid₀ α} {f : α → β} :
  f <$> (℘ g) = ℘ (f <$> g) :=
  by simpa [(<$>), generate, abs_data, contents, vector.nth_map, (∘)]

lemma map_generate_map_f₀ {α β : Type} (g : fgrid₀ α) {f : α → β} :
  f <$> (℘ g) = ℘ (f <$> g) :=
  by simpa [(<$>), generate, abs_data, contents]

lemma dec_grid_len_eq_indices_len :
  length (℘ g) = length (gip_g g) :=
  by simp [length_generate, length_gip_g]

def vec_grid₀_of_fgrid₀ {α : Type} (g : fgrid₀ α) : vec_grid₀ α :=
  {g with contents := ⟨℘ g, length_generate_eq_size _⟩}

def fgrid₀_of_vec_grid₀ {α : Type} (g : vec_grid₀ α) : fgrid₀ α :=
  {g with contents := λx y, abs_data g ⟨x, y⟩}

def dep_vec_grid₀_of_fgrid₀ {α : Type} (g : fgrid₀ α) : dep_vec_grid α g.r g.c :=
  {g with contents := ⟨℘ g, length_generate_eq_size _⟩}

def vec_grid_of_dep_vec_grid {m n} {α : Type} (g : dep_vec_grid α m n) : vec_grid₀ α :=
  ⟨⟨m, n, g.1, g.2⟩, ⟨0, 0⟩⟩

instance f₀_v₀_coe {α : Type} : has_coe (fgrid₀ α) (vec_grid₀ α) := ⟨vec_grid₀_of_fgrid₀⟩
instance v₀_f₀_coe {α : Type} : has_coe (vec_grid₀ α) (fgrid₀ α) := ⟨fgrid₀_of_vec_grid₀⟩

attribute [simp]
lemma vec_grid₀_of_fgrid₀_r {α : Type} {g : fgrid₀ α} :
  (vec_grid₀_of_fgrid₀ g).r = g.r := by simp [vec_grid₀_of_fgrid₀]

attribute [simp]
lemma vec_grid₀_of_fgrid₀_c {α : Type} {g : fgrid₀ α} :
  (vec_grid₀_of_fgrid₀ g).c = g.c := by simp [vec_grid₀_of_fgrid₀]

attribute [simp]
lemma vec_grid₀_of_fgrid₀_o {α : Type} {g : fgrid₀ α} :
  (vec_grid₀_of_fgrid₀ g).o = g.o := by simp [vec_grid₀_of_fgrid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_r {α : Type} {g : vec_grid₀ α} :
  (fgrid₀_of_vec_grid₀ g).r = g.r := by simp [fgrid₀_of_vec_grid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_c {α : Type} {g : vec_grid₀ α} :
  (fgrid₀_of_vec_grid₀ g).c = g.c := by simp [fgrid₀_of_vec_grid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_o {α : Type} {g : vec_grid₀ α} :
  (fgrid₀_of_vec_grid₀ g).o = g.o := by simp [fgrid₀_of_vec_grid₀]

attribute [simp]
lemma vec_grid₀_of_fgrid₀_gtr {α : Type} {g : fgrid₀ α} :
  gtr (vec_grid₀_of_fgrid₀ g) = gtr g :=
    by simp [expand_gtr, bl, cols, rows, vec_grid₀_of_fgrid₀]

attribute [simp]
lemma fgrid₀_of_vec_grid₀_gtr {α : Type} {g : vec_grid₀ α} :
  gtr (fgrid₀_of_vec_grid₀ g) = gtr g :=
    by simp [expand_gtr, bl, cols, rows, fgrid₀_of_vec_grid₀]

private theorem nth_le_grp {n} {a b r : ℤ} (h : a < b) (H) :
  nth_le (grp a b r) n H = ⟨a + n, r⟩ :=
begin
  rw ← option.some_inj, rw ← nth_le_nth H,
  induction n with n ih generalizing a b,
    {simp [expand_grp h]},
    {
      simp [expand_grp h],
      have : a + 1 < b,
        begin
          have : a + 1 ≠ b, assume contra, by
            simp [contra.symm, @length_grp a (a + 1) (by cc)] at H;
            clear contra h ih; omega,
          by_contradiction h₁,
          replace h₁ := le_of_not_lt h₁,
          rw le_iff_eq_or_lt at h₁, cases h₁; try { cc },
          have : a = b, by linarith, rw [this, length_grp] at H,
          simp at H, cases H, linarith
        end,
      have lenok : n < length (grp (a + 1) b r),
        begin
          rw length_grp this, rw length_grp h at H,
          have eq₁ : b - (a + 1) ≥ 0, by linarith,
          have eq₂ : b - a ≥ 0, by linarith,
          rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg eq₁],
          rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg eq₂] at H,
          simp, simp at H, linarith
        end,
      specialize @ih (a + 1) b this lenok,
      simp [ih]
    }
end

theorem nth_grp {n} {a b r : ℤ} (h : a < b) (H : n < length (grp a b r)) :
  nth (grp a b r) n = some ⟨a + n, r⟩ :=
  by rw nth_le_nth H; exact congr_arg _ (nth_le_grp h _)

theorem nth_le_gip {n} {p₁ p₂ : point} (h : p₁ ↗ p₂) (H) :
  nth_le (gip p₁ p₂) n H =
  ⟨p₁.x + n % |p₂.x - p₁.x|, p₁.y + n / |p₂.x - p₁.x|⟩ :=
begin
  cases p₁ with x₁ y₁, cases p₂ with x₂ y₂,
  have x₁x₂ : x₁ < x₂, from (grid_bounded_iff.1 h).1,
  have y₁y₂ : y₁ < y₂, from (grid_bounded_iff.1 h).2,
  rw [← option.some_inj, ← nth_le_nth H], rw length_gip h at H,
  repeat { rw nat_abs_of_nonneg (nonneg_of_lt x₁x₂) },
  simp [-sub_eq_add_neg] at *,
  have : y₂ = y₁ + (y₂ - y₁), by linarith,
  rw this, clear this,
  have : y₂ - y₁ = ↑|y₂ - y₁|,
    by rw nat_abs_of_nonneg; exact nonneg_of_lt y₁y₂,
  rw this, clear this,
  generalize hrows : |y₂ - y₁| = rows, rw hrows at H,
  induction rows with rows ih generalizing y₁ y₂ n,
    {exfalso, simp at H, cases H},
    {
      rw expand_row_gip _,
        {
          by_cases h₁ : n < |x₂ - x₁|,
            {
              simp [-sub_eq_add_neg], rw [nth_split, nth_grp];
              try {simpa [length_grp x₁x₂]},
              congr' 2;
              rw [
                ← int.coe_nat_lt_coe_nat_iff,
                nat_abs_of_nonneg (nonneg_of_lt x₁x₂)
              ] at h₁,
              rw mod_eq_of_lt (coe_zero_le _) h₁,
              rw div_eq_zero_of_lt (coe_zero_le _) h₁,
              simp
            },
            {
              generalize hcols : x₂ - x₁ = cols,
              have rowsnezero : rows ≠ 0, assume contra,
                by simp [contra, -sub_eq_add_neg] at H; contradiction,
              have colsnezero : cols ≠ 0, by linarith,
              have x₂x₁n : |x₂ - x₁| ≤ n, from not_lt.1 h₁,
              have lenok : ¬n < length (grp x₁ x₂ y₁),
                by simpa [length_grp x₁x₂, -sub_eq_add_neg],
              simp [-sub_eq_add_neg], rw nth_split_second lenok,
              by_cases h₂ : y₁ + 1 < y₂,
                {
                  have h₃ : {x := x₁, y := y₁ + 1}↗{x := x₂, y := y₂},
                    from ⟨x₁x₂, h₂⟩,
                  have lenok :
                    n - length (grp x₁ x₂ y₁) < rows * |x₂ - x₁|,
                    {
                      rw nat.succ_mul at H,
                      rw [
                        length_grp x₁x₂, ← int.coe_nat_lt_coe_nat_iff,
                        int.coe_nat_sub x₂x₁n, int.coe_nat_mul,
                        sub_lt_iff_lt_add, ← int.coe_nat_mul, ← int.coe_nat_add
                      ],
                      rwa int.coe_nat_lt_coe_nat_iff
                    },
                  have rowsok : |y₂ - (y₁ + 1)| = rows,
                    by rw [← abs_minus_plus y₁y₂, hrows, nat.succ_sub_one],
                  rw [
                    ← add_assoc,
                    @ih (y₁ + 1) y₂ (n - length (grp x₁ x₂ y₁)) h₃ h₂ rowsok lenok,
                    length_grp x₁x₂
                  ],
                  simp [-sub_eq_add_neg],
                  exact ⟨
                    begin
                      rw [
                        int.coe_nat_sub x₂x₁n, nat_abs_of_nonneg, ← hcols,
                        mod_eq_mod_iff_mod_sub_eq_zero, mod_eq_zero_of_dvd
                      ],
                      simp, rw ← dvd_neg, simp,
                      exact nonneg_of_lt x₁x₂
                    end,
                    begin
                      rw [
                        int.coe_nat_sub x₂x₁n,
                        nat_abs_of_nonneg (nonneg_of_lt x₁x₂), hcols
                      ],
                      simp,
                      have : -cols = cols * (-1 : ℤ), by simp, rw this,
                      rw int.add_mul_div_left _ _ colsnezero,
                      simp
                    end
                  ⟩
                },
                {
                  have h₃ : y₁ + 1 = y₂, by linarith,
                  have h₄ : |y₂ - y₁| = 1, by simp [h₃.symm, add_sub_cancel'],
                  rw h₄ at hrows, injection hrows with contra, cc
                }
            }
      },
      {
        exact ⟨
          (grid_bounded_iff.1 h).1,
          begin
            simp [
              sub_lt_iff_lt_add, lt_add_iff_pos_right, -sub_eq_add_neg
            ],
            exact nat.cases_on rows
              zero_lt_one
              (λ_, lt_trans zero_lt_one (lt_add_succ _ _)),
          end
        ⟩
      }
    }
end

theorem nth_le_gip_g {n} (H) :
  nth_le (gip_g g) n H = ⟨(bl g).x + n % cols g, (bl g).y + n / cols g⟩ :=
begin
  rw cols_eq_trx_sub_blx,
  exact @nth_le_gip n (gbl g) (gtr g) grid_is_bounding_box H
end

theorem nth_generate {n} (H) :
  nth_le (℘ g) n H =
  abs_data g ⟨
    ⟨(bl g).y + n / cols g, ⟨
      by simp,
      idx_div_cols_bounded (by rwa length_generate_eq_size at H)
    ⟩⟩,
    ⟨(bl g).x + n % cols g, ⟨
      by simp,
      idx_mod_cols_bounded⟩
  ⟩⟩ :=
begin
  rw length_generate at H,
  rw [← option.some_inj, ← nth_le_nth],
  simp only [
    abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, expand_gtr,
    generate, nth_map
  ],
  have : n < length (attach (gip_g g)), by simpa [length_attach, length_gip_g],
  simp [
    nth_le_nth this, inject_into_bounded, make_bounded_idx, make_bounded,
    nth_le_gip_g, grid_point_of_prod, data_option
  ]
end

theorem nth_generate' {n} (h : n < length ℘ g) :
  nth (℘ g) n = 
  some (abs_data g ⟨
    ⟨(bl g).y + n / cols g, ⟨
      by simp,
      idx_div_cols_bounded (by rwa length_generate_eq_size at h)
    ⟩⟩,
    ⟨(bl g).x + n % cols g, ⟨
      by simp,
      idx_mod_cols_bounded⟩
  ⟩⟩) := by simp [nth_le_nth h, congr_arg, nth_generate]

lemma abs_data_eq_nth_v₀ {α : Type} {g : vec_grid₀ α} {p} :
  abs_data g p = vector.nth g.contents (grid_point_to_fin p) :=
  by simpa [
       abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, contents,
       grid_point_to_fin, rel_point_to_fin
     ]

lemma abs_data_eq_nth_v₀' {α : Type} {g : vec_grid₀ α} {p} :
  abs_data g p =
  vector.nth g.contents ⟨|p.y.1 - g.o.y| * g.c + |p.x.1 - g.o.x|,
  begin
    rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, ⟨y, ⟨yl, yu⟩⟩⟩,
    simp [-sub_eq_add_neg],
    simp [-sub_eq_add_neg, expand_gtr, bl, rows, cols] at *,
    rw add_comm,
    have eq₁ : |y - g.o.x| < g.c,
      {
        have : y - (g.o).x ≥ 0, by linarith,
        rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg this],
        linarith
      },
    have eq₂ : |x - g.o.y| < g.r,
      {
        have : x - g.o.y ≥ 0, by linarith,
        rw [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg this],
        linarith
      },
    exact linearize_array eq₁ eq₂
  end⟩ :=
  by simp [
       abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, contents,
       grid_point_to_fin, rel_point_to_fin, bl, rows, cols
     ]

lemma abs_data_eq_nth_f₀ {α : Type} {g : fgrid₀ α} {p} :
  abs_data g p = g.contents p.y p.x :=
begin
  rcases p with ⟨⟨x, ⟨xl, xu⟩⟩, ⟨y, ⟨yl, yu⟩⟩⟩,
  simp only [
    abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point, contents
  ],
  unfold_coes, simp only [fin.val, of_nat_eq_coe],
  have h₁ : x - (bl g).y ≥ 0, by linarith,
  have h₂ : y - (bl g).x ≥ 0, by linarith,
  congr; rw int.nat_abs_of_nonneg; try { assumption };
  simp only [bl];
  linarith
end

lemma some_nth_le_generate_v₀ {α : Type} {g : vec_grid₀ α} {n} (H) :
  some (nth_le (℘ g) n H) =
  nth g.contents.to_list ( |↑n % ↑g.c| + |↑n / ↑g.c| * g.c ) :=
begin
  rcases g with ⟨⟨r, c, h, ⟨d, hd⟩⟩, o⟩,
  rw [nth_le_nth, nth_generate],
  simp [abs_data_eq_nth_v₀', expand_gtr, bl, rows, cols, vector.nth, hd],
  rw mod_add_div_coe,
  simp [length_generate, rows, cols] at H,
  simp [H], simpa [hd]
end

lemma nth_generate_v₀ {α : Type} {g : vec_grid₀ α} {n} (H : n < length ℘ g):
  nth (℘ g) n =
  nth g.contents.to_list ( |↑n % ↑g.c| + |↑n / ↑g.c| * g.c) :=
  by simp [nth_le_nth, some_nth_le_generate_v₀, H]

private lemma goy_add_n_div_c_lt_goy_add_r {α : Type} {g : fgrid₀ α} {n : ℕ}
  (h : n < length ℘ g) : g.o.y + ↑n / ↑g.c < g.o.y + ↑g.r :=
  begin
    simp [-sub_eq_add_neg], norm_cast,
    rw [length_generate, nat.mul_comm] at h,
    exact nat.div_lt_of_lt_mul h
  end

lemma some_nth_le_generate_f₀ {α : Type} {g : fgrid₀ α} {n} (H) :
  some (nth_le (℘ g) n H) =
  g.contents
    ⟨g.o.y + ↑n / ↑g.c, ⟨by simp, goy_add_n_div_c_lt_goy_add_r H⟩⟩
    ⟨g.o.x + ↑n % ↑g.c, ⟨by simp, by simp; exact mod_lt_of_pos _ coe_cols_pos_f⟩⟩
  := by simpa [nth_generate, abs_data_eq_nth_f₀, expand_gtr]

lemma nth_generate_f₀ {α : Type} {g : fgrid₀ α} {n} (H : n < length ℘ g) :
  nth (℘ g) n =
  g.contents
    ⟨g.o.y + ↑n / ↑g.c, ⟨by simp, goy_add_n_div_c_lt_goy_add_r H⟩⟩
    ⟨g.o.x + ↑n % ↑g.c, ⟨by simp, by simp; exact mod_lt_of_pos _ coe_cols_pos_f⟩⟩
  := by simp [nth_le_nth H, some_nth_le_generate_f₀]

lemma nth_le_generate_f₀ {α : Type} {g : fgrid₀ α} {n} (H) :
  nth_le (℘ g) n H =
  g.contents
    ⟨g.o.y + ↑n / ↑g.c, ⟨by simp, goy_add_n_div_c_lt_goy_add_r H⟩⟩
    ⟨g.o.x + ↑n % ↑g.c, ⟨by simp, by simp; exact mod_lt_of_pos _ coe_cols_pos_f⟩⟩
  := by simpa [nth_generate, abs_data_eq_nth_f₀, expand_gtr]

lemma generate_eq_data {α : Type} (g : vec_grid₀ α) :
  ℘ g = g.contents.to_list :=
begin
  have h₁ : length (℘ g) = rows g * cols g,
    from length_generate _,
  have h₂ : length (g.contents.to_list) = rows g * cols g,
    by simp [rows, cols],
  apply ext_le (eq.trans h₁ h₂.symm) (λi hi₁ hi₂, _),
  rw h₁ at hi₁, rw h₂ at hi₂,
  have : hi₁ = hi₂, from rfl, subst this, dedup,
  rw ← option.some_inj, repeat { rw ← nth_le_nth },
  rename hi₁_1 hi,
  rcases g with ⟨⟨r, c, h, ⟨contents, hd⟩⟩, o⟩,
  simp [-sub_eq_add_neg, rows, cols] at *,
  rw [nth_le_nth (by simpa [length_generate_eq_sizes]), some_nth_le_generate_v₀],
  rw nth_le_nth hi₂, simp,
  have : |↑i % ↑c| + |↑i / ↑c| * c = i, from mod_add_div_coe,
  repeat { rw ← nth_le_nth }, simp [this]
end

private theorem generate_inj_v₀_v₀ {α : Type} {g₁ g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = ℘ g₂) : g₁ = g₂ :=
begin
  repeat { rw generate_eq_data at h },
  rcases g₁ with ⟨⟨g₁r, g₁c, g₁h, g₁d⟩, g₁o⟩,
  rcases g₂ with ⟨⟨g₂r, g₂c, g₂h, g₂d⟩, g₂o⟩,
  dsimp at hrows hcols horig h,
  substs hrows hcols horig,
  congr, exact vector.to_list_inj h
end

theorem grid_eq_iff_v₀_v₀ {α : Type} {g₁ g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
  ⟨λh, h ▸ rfl, generate_inj_v₀_v₀ hrows hcols horig⟩

private theorem generate_inj_f₀_f₀ {α : Type} {g₁ g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = ℘ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c,
    from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c,
    from length_generate _,
  cases g₁ with g₁r g₁c g₁h g₁o g₁d,
  cases g₂ with g₂r g₂c g₂h g₂o g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  congr, ext x y,
  rcases x with ⟨x, ⟨xl, xu⟩⟩, rcases y with ⟨y, ⟨yl, yu⟩⟩,
  have rowsnezero : g₁r ≠ 0, assume contra,
    by simp [contra] at g₁h; exact absurd g₁h (lt_irrefl _),
  have colsnezero : g₁c ≠ 0, assume contra,
    by simp [contra] at g₂h; exact absurd g₂h (lt_irrefl _),
  let i := |x - g₁o.y| * g₁c + |y - g₁o.x|,
  have hi : i = |x - g₁o.y| * g₁c + |y - g₁o.x|, refl,
  have r_nonneg : x - g₁o.y ≥ 0,
    by simp only [ge_from_le, le_sub_iff_add_le, zero_add]; exact xl,
  have c_nonneg : y - g₁o.x ≥ 0,
    by simp only [ge_from_le, le_sub_iff_add_le, zero_add]; exact yl,
  have i_nonneg : 0 ≤ i, by linarith,
  have i_bounded : i < g₁r * g₁c,
    {
      have yb : y - g₁o.x < ↑g₁c, from sub_lt_iff_lt_add'.2 yu,
      have xb : x - g₁o.y < ↑g₁r, from sub_lt_iff_lt_add'.2 xu,
      rw hi,
      apply linearize_array;
        try { rw ← int.coe_nat_lt_coe_nat_iff };
        rw nat_abs_of_nonneg; try { assumption }
    },
  have h₁ : ∀hh,
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₁h, o := g₁o, contents := g₁d} : fgrid₀ α
    )) i hh =
    list.nth_le (℘ (
      {r := g₁r, c := g₁c, h := g₂h, o := g₁o, contents := g₂d} : fgrid₀ α
    )) i (hl₂.symm ▸ i_bounded), { rw h, intro, refl },
  specialize h₁ (hl₁.symm ▸ i_bounded),
  simp [-sub_eq_add_neg, nth_le_generate_f₀] at h₁,
  have : g₁o.y + (↑|y - g₁o.x| + ↑|x - g₁o.y| * ↑g₁c) / ↑g₁c = x,
    {
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      rw @int.add_mul_div_right _ _ ↑g₁c (by simp [colsnezero]),
      rw div_eq_zero_of_lt c_nonneg (sub_lt_iff_lt_add'.2 yu),
      simp
    },
  simp only [this] at h₁,
  have : g₁o.x + ↑|y - g₁o.x| % ↑g₁c = y,
    {
      repeat { rw nat_abs_of_nonneg; try { assumption } },
      rw mod_eq_of_lt c_nonneg (sub_lt_iff_lt_add'.2 yu),
      simp
    },
  simp only [this] at h₁,
  exact h₁
end

theorem grid_eq_iff_f₀_f₀ {α : Type} {g₁ g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
  ⟨λh, h ▸ rfl, generate_inj_f₀_f₀ hrows hcols horig⟩

def row (n : fin (rows g)) :
  (fin (cols g)) → carrier α :=
  contents g n

def col (n : fin (cols g)) :
  (fin (rows g)) → carrier α :=
  flip (contents g) n

def top :=
  row g ⟨
    0,
    and.elim_left (gt_and_gt_of_mul_gt (nonempty g))
  ⟩

def bot :=
  row g ⟨nat.pred (rows g),
         nat.pred_lt (ne_of_gt (gt_and_gt_of_mul_gt (nonempty g)).1)
        ⟩

def left :=
  have h : cols g > 0,
    from (gt_and_gt_of_mul_gt (nonempty g)).2,
  col g ⟨0, h⟩

def right :=
  have h : cols g > 0,
    from (gt_and_gt_of_mul_gt (nonempty g)).2,
  col g ⟨nat.pred (cols g), nat.pred_lt (ne_of_gt h)⟩

def grid_bounds : bounding_box :=
  ⟨gbl g, gtr g, grid_is_bounding_box⟩

def overlaid_by (bb₁ bb₂ : bounding_box) :=
  (bb₂.p₁.x ≤ bb₁.p₁.x ∧ bb₁.p₂.x ≤ bb₂.p₂.x) ∧
  (bb₁.p₂.y ≤ bb₂.p₂.y ∧ bb₂.p₁.y ≤ bb₁.p₁.y)

def in_grid_bounded (p : point)
  (h : is_in_grid' g p) :=
  let ⟨left, right⟩ :=
    h in (make_bounded left, make_bounded right)

instance overlaid_decidable (p₁ p₂ : bounding_box) :
  decidable (overlaid_by p₁ p₂) := by simp [overlaid_by]; apply_instance

lemma overlaid_by_refl (bb : bounding_box) : overlaid_by bb bb :=
  by simp [overlaid_by]; repeat {split}; refl

lemma overlaid_by_trans {bb₁ bb₂ bb₃ : bounding_box}
  (h : overlaid_by bb₁ bb₂) (h₁ : overlaid_by bb₂ bb₃) : overlaid_by bb₁ bb₃ :=
  by simp [overlaid_by] at *; repeat {split}; transitivity; finish

lemma overlaid_by_antisymm {bb₁ bb₂ : bounding_box}
  (h : overlaid_by bb₁ bb₂) (h₁ : overlaid_by bb₂ bb₁) : bb₁ = bb₂ :=
begin
  simp [overlaid_by] at *,
  rcases bb₁ with ⟨⟨_, _⟩, ⟨_, _⟩⟩, rcases bb₂ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  safe
end

lemma is_in_larger {bb₁ bb₂ : bounding_box} {xy : point}
  (h : xy ∈ bb₁) (h₁ : overlaid_by bb₁ bb₂) : xy ∈ bb₂ :=
  ⟨⟨le_trans h₁.2.2 h.1.1, lt_of_lt_of_le h.1.2 h₁.2.1⟩,
   ⟨le_trans h₁.1.1 h.2.1, lt_of_lt_of_le h.2.2 h₁.1.2⟩⟩

private def bounded_prod_of_point {p : point} {g : α} (h : p ∈ g) :
  bounded (bl g).x (gtr g).x ×
  bounded (bl g).y (gtr g).y := ⟨make_bounded h.2, make_bounded h.1⟩

open bounding_box

def subgrid {α : Type*} [grid α] (g : α)
            (bb : bounding_box)
            (h : overlaid_by bb (bbox_of_grid g)) :
            fgrid₀ (carrier α) :=
  ⟨rows_of_box bb, cols_of_box bb,
   mul_pos rows_of_box_pos cols_of_box_pos, bb.p₁,
   λx y, abs_data g ⟨⟨x.1,
    begin
      unfold overlaid_by at h, cases x with x hx, simp,
      rw bbox_of_grid_p₁ at h, rw bbox_of_grid_p₂ at h,
      exact ⟨
        le_trans h.2.2 hx.1,
        begin
          have : bb.p₁.y + ↑(rows_of_box bb) = bb.p₂.y,
            begin
              have : (bb.p₂).y - (bb.p₁).y ≥ 0,
                by simp [-sub_eq_add_neg, ge_from_le];
                   apply int.le_of_lt (grid_bounded_iff.1 bb.3).2,
              simp [-sub_eq_add_neg, rows_of_box],
              rw nat_abs_of_nonneg this,
              simp
            end, rw this at hx,
          exact lt_of_lt_of_le hx.2 h.2.1
        end
      ⟩
    end⟩, ⟨y.1,
    begin
      unfold overlaid_by at h, cases y with y hy, simp,
      rw bbox_of_grid_p₁ at h, rw bbox_of_grid_p₂ at h, 
      have : (bb.p₁).x + ↑(cols_of_box bb) = bb.p₂.x,
        by simp [
             -sub_eq_add_neg, bounding_box.p₁, bounding_box.p₂, cols_of_box,
             nat_abs_of_nonneg (nonneg_of_lt (grid_bounded_iff.1 bb.3).1),
             add_sub_cancel'_right
           ], rw this at hy,
      exact ⟨le_trans h.1.1 hy.1, lt_of_lt_of_le hy.2 h.1.2⟩
    end⟩⟩⟩

private def modify_vec
  {α : Type} {m} (v : vector α m) (n : ℕ) (x : α) : vector α m :=
  ⟨update_nth v.to_list n x,
   by simp [update_nth_pres_len, *]⟩

def modify_at {α : Type} (p : point) (x : α) (g : vec_grid₀ α) : vec_grid₀ α :=
  if h : p ∈ g
  then let ⟨r, c⟩ :=
         relpoint_of_gpoint $
           @grid_point.mk _ _ g
           ⟨p.y, by simp only [(∈)] at h; exact h.left⟩
           ⟨p.x, by simp only [(∈)] at h; exact h.right⟩ in
    ⟨⟨g.r, g.c, g.h, modify_vec g.contents (r * g.c + c) x⟩, g.o⟩
  else g

def modify_many {α : Type} (l : list (point × α)) (g : vec_grid₀ α) : vec_grid₀ α :=
  foldr (uncurry modify_at) g l

def count_grid {α : Type} [grid α] [decidable_eq (carrier α)]
  (g : α) (x : carrier α) := list.count x (℘ g)

lemma gen_aof_eq_gen {α : Type} {g : fgrid₀ α} :
  ℘ (vec_grid₀_of_fgrid₀ g) = @generate _ ag_fgrid₀ g :=
  by simp [vec_grid₀_of_fgrid₀, generate_eq_data]

private theorem generate_inj_a_f {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = @generate (fgrid₀ α) _ g₂) : g₁ = g₂ :=
begin
  have hl₁ : length (℘ g₁) = g₁.r * g₁.c, from length_generate _,
  have hl₂ : length (℘ g₂) = g₂.r * g₂.c, from length_generate _,
  rcases g₁ with ⟨⟨g₁r, g₁c, g₁h, ⟨g₁dv, g₁dh⟩⟩, g₁o⟩,
  cases g₂ with g₂r g₂c g₂h g₂o g₂d,
  dsimp at hrows hcols horig hl₁ hl₂,
  subst hrows, subst hcols, subst horig,
  unfold_coes,
  simp [vec_grid₀_of_fgrid₀, h.symm, generate_eq_data]
end

lemma gen_foa_eq_gen {α : Type} {g : vec_grid₀ α} :
  ℘ (fgrid₀_of_vec_grid₀ g) = @generate (vec_grid₀ α) _ g :=
begin
  have hl₁ : length (℘ g) = rows g * cols g,
    from length_generate _,
  have hl₂ : length (℘ (fgrid₀_of_vec_grid₀ g)) = rows g * cols g,
    from length_generate _,
  simp [fgrid₀_of_vec_grid₀] at *,
  apply list.ext_le (hl₂.trans hl₁.symm) (λi hi₁ hi₂, _),
  simp [
    nth_le_generate_f₀, nth_generate, abs_data_eq_nth_v₀', abs_data_eq_nth_f₀,
    tl, bl, rows, cols, expand_gtr
  ]
end

private theorem generate_inj_f₀_v₀ {α : Type} {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o)
  (h : ℘ g₁ = @generate (fgrid₀ α) _ g₂) : g₁ = g₂ :=
  generate_inj_f₀_f₀ hrows hcols horig h

theorem grid_eq_iff_v₀_f₀
  {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α}
  (h₁ : g₁.r = g₂.r)
  (h₂ : g₁.c = g₂.c)
  (h₃ : g₁.o = g₂.o) :
  g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
  ⟨λh, h ▸ rfl, λh, generate_inj_a_f h₁ h₂ h₃ $ by rwa gen_aof_eq_gen.symm⟩ 

theorem grid_eq_iff_f₀_v₀
  {α : Type} {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α}
  (h₁ : g₁.r = g₂.r)
  (h₂ : g₁.c = g₂.c)
  (h₃ : g₁.o = g₂.o) :
  g₁ = g₂ ↔ ℘ g₁ = ℘ g₂ :=
    ⟨λh, h ▸ rfl, λh, generate_inj_f₀_v₀ h₁ h₂ h₃ h⟩ 

attribute [extensionality]
theorem grid_eq_ext_v₀_v₀ {α : Type} {g₁ g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_v₀_v₀ hrows hcols horig).2

attribute [extensionality]
theorem grid_eq_ext_f₀_f₀ {α : Type} {g₁ g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_f₀_f₀ hrows hcols horig).2

attribute [extensionality]
theorem grid_eq_ext_v₀_f₀ {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_v₀_f₀ hrows hcols horig).2

attribute [extensionality]
theorem grid_eq_ext_f₀_v₀ {α : Type} {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α}
  (hrows : g₁.r = g₂.r)
  (hcols : g₁.c = g₂.c)
  (horig : g₁.o = g₂.o) : ℘ g₁ = ℘ g₂ → g₁ = g₂ :=
  (grid_eq_iff_f₀_v₀ hrows hcols horig).2

lemma nth_vecgrid_of_fgrid {α : Type} {g : fgrid₀ α} {n} :
  list.nth (vec_grid₀_of_fgrid₀ g).contents.val n = list.nth (℘ g) n :=
  by delta vec_grid₀_of_fgrid₀; simp

instance decidable_eq_v₀_v₀ {α : Type} [decidable_eq α]
  : decidable_eq (vec_grid₀ α) :=
  λg₁ g₂, if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
            by simp [grid_eq_iff_v₀_v₀, *]; apply_instance
          else is_false $ by finish

instance decidable_eq_f₀_f₀ {α : Type} [decidable_eq α]
  : decidable_eq (fgrid₀ α) :=
  λg₁ g₂, if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
            by simp [grid_eq_iff_f₀_f₀, *]; apply_instance
          else is_false $ by finish

instance decidable_eq_v₀_f₀ {α : Type} [decidable_eq α]
  {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α} : decidable (g₁ = g₂) :=
  if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
    by simp [grid_eq_iff_v₀_f₀, *]; apply_instance    
  else is_false $ by finish

instance decidable_eq_f₀_v₀ {α : Type} [decidable_eq α]
  {g₁ : fgrid₀ α} {g₂ : vec_grid₀ α} : decidable (g₁ = g₂) :=
  if h : g₁.r = g₂.r ∧ g₁.c = g₂.c ∧ g₁.o = g₂.o then
    by simp [grid_eq_iff_f₀_v₀, *]; apply_instance
  else is_false $ by finish

lemma subgrid_self {α : Type} {g : vec_grid₀ α} {bb : bounding_box}
  (h : bb = {bounding_box. p₁ := bl g, p₂ := gtr g, h := grid_is_bounding_box })
  : subgrid g bb begin unfold bbox_of_grid, rw h, exact overlaid_by_refl _ end =
    g :=
begin
  rcases g with ⟨⟨r, c, h, ⟨d, hd⟩⟩, o⟩,
  simp [h, subgrid], unfold_coes,
  rw grid_eq_iff_f₀_f₀;
    try { simp [cols_of_box, bl, expand_gtr, cols] };
    try { simp };
    try { simp [rows_of_box, bl, expand_gtr, rows] },
  rw gen_foa_eq_gen,
  apply ext_le,
    {
      simp [
        length_generate_eq_size, size, rows, cols,
        rows_of_box, cols_of_box, bl, expand_gtr
      ]
    },
    {
      intros,
      rw nth_le_generate_f₀, 
      simp only [
        nth_generate, abs_data, contents, expand_gtr, bl, (∘),
        relpoint_of_gpoint, prod_of_rel_point, rows, cols, tl,
        rows_of_box, cols_of_box
      ], simp
    }
end

lemma p_in_g_iff_v₀_f₀ {α : Type} {g₁ : vec_grid₀ α} {g₂ : fgrid₀ α} {p}
                     (h₁ : g₁.r = g₂.r)
                     (h₂ : g₁.c = g₂.c)
                     (h₃ : g₁.o = g₂.o) : p ∈ g₁ ↔ p ∈ g₂ :=
begin
  rcases g₁ with ⟨⟨r₁, c₁, gh₁, d₁⟩, o₁⟩,
  rcases g₂ with ⟨r₂, c₂, gh₂, o₂, d₂⟩,
  simp [flip, is_in_grid'] at *,
  split; intros; unfold_projs at *;  
  subst h₁; subst h₂; subst h₃; finish
end

end finite_grid

section grid_instances

open relative_grid

def split_rows_cols : ℕ → ℕ → list string → list string
  | cols 0 ls := [""]
  | cols (k + 1) ls := list.take cols ls ++ ["\n"]
                       ++ split_rows_cols cols k (list.drop cols ls)

def grid_str {α : Type*} [grid α]
  [has_to_string (carrier α)] (g : α) : string :=
  let points := list.map to_string $ ℘ g in
    " " ++ (list.foldr append "" $
                       list.intersperse " " $
                       split_rows_cols (cols g)
                                       (rows g) points)

instance grid_repr {α : Type*} [grid α]
  [has_to_string (carrier α)] : has_repr α := ⟨grid_str⟩ 

instance grid_to_string {α : Type*} [grid α]
  [has_to_string (carrier α)] : has_to_string α := ⟨grid_str⟩ 

end grid_instances