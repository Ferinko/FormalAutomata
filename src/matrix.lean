-- Formalization of matrices defined over 'grid's.

import grid utils data.vector2 tactic.elide

open utils

namespace matrix

structure matrix (m n : ℕ) (α : Type) :=
  (g  : dep_vec_grid α m n)

private lemma matrix_of_f_ {x : ℤ} {m} (h : x < ↑m) (h₁ : 0 ≤ x) : |x| < m :=
  by rwa [← int.coe_nat_lt_coe_nat_iff, int.nat_abs_of_nonneg h₁]

def matrix_of_f {m n} {α} (h : m * n > 0) (f : fin m → fin n → α) : matrix m n α :=
  ⟨⟨h, ⟨℘(fgrid₀.mk m n h ⟨0, 0⟩
    (λx y, f 
      ⟨|x.1|,
         begin
           rcases x with ⟨x, ⟨hx₁, hx₂⟩⟩, simp at hx₁ hx₂ ⊢, 
           exact matrix_of_f_ hx₂ hx₁
         end
       ⟩
      ⟨|y.1|,
         begin
           rcases y with ⟨y, ⟨hy₁, hy₂⟩⟩, simp at hy₁ hy₂ ⊢, 
           exact matrix_of_f_ hy₂ hy₁
         end
      ⟩)), by simpa [length_generate_eq_size, size]⟩⟩⟩

private lemma matrix_at_ {m n} {α} (m₁ : matrix m n α) (i : fin m) :
  (grid.bl (vec_grid_of_dep_vec_grid (m₁.g))).y ≤ ↑(i.val) ∧
  ↑(i.val) < (gtr (vec_grid_of_dep_vec_grid (m₁.g))).y :=
begin
  rcases m₁ with ⟨⟨h, ⟨d, hd⟩⟩⟩,
  simp [grid.bl, expand_gtr, relative_grid.rows, vec_grid_of_dep_vec_grid],
  norm_cast,
  exact ⟨zero_le _, i.2⟩
end

private lemma matrix_at_ {m n} {α} (m₁ : matrix m n α) (j : fin n) :
  (grid.bl (vec_grid_of_dep_vec_grid (m₁.g))).x ≤ ↑(j.val) ∧
  ↑(j.val) < (gtr (vec_grid_of_dep_vec_grid (m₁.g))).x :=
begin
  rcases m₁ with ⟨⟨h, ⟨d, hd⟩⟩⟩,
  simp [grid.bl, expand_gtr, relative_grid.rows, vec_grid_of_dep_vec_grid],
  norm_cast,
  exact ⟨zero_le _, j.2⟩
end

def matrix_at {m n} {α} (m₁ : matrix m n α) (i : fin m) (j : fin n) : α :=
  abs_data (vec_grid_of_dep_vec_grid m₁.1)
    ⟨⟨i.1, matrix_at_ m₁ i⟩, ⟨j.1, matrix_at_ m₁ j⟩⟩

@[simp]
lemma matrix_get_mk {α} {m n} (h : m * n > 0)
  (f : fin m → fin n → α) (i : fin m) (j : fin n) :
  matrix_at (matrix_of_f h f) i j = f i j :=
begin
  simp [matrix_of_f, matrix_at], unfold_projs,
  delta vec_grid_of_dep_vec_grid, unfold_projs,
  rw abs_data_eq_nth_v₀, unfold_projs,
  simp [
    vector.nth, nth_generate, grid.bl, relative_grid.cols,
    grid_point_to_fin, rel_point_to_fin, relpoint_of_gpoint,
    abs_data, relative_grid.contents
  ],
  cases i with i hi, cases j with i hj,
  have intzero_add : ∀x, int.zero + x = x,
    by intros; simp [int.zero]; rw int.of_nat_eq_coe; ring,
  congr,
    {
      simp, norm_cast,
      have : ↑i + -int.zero = ↑i, by ring, simp [this, intzero_add],
      unfold_coes, simp [fin.val],
      rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_div, int.coe_nat_add], simp,
      have h₁ : int.of_nat i + -int.zero = ↑i, by ring,
      have : int.of_nat i + -int.zero ≥ (0 : ℤ), by norm_cast,
      rw int.nat_abs_of_nonneg, swap 2, exact this,
      have : ↑n ≠ (0 : ℤ), by simp; clear_except h; intros contra; subst contra; linarith,
      rw int.add_mul_div_right _ _ this,
      have : ↑i / ↑n = (0 : ℤ), by norm_cast; exact nat.div_eq_of_lt hj, simp [this],
      ring
    },
    {
      have : -int.zero = int.zero, by refl, simp [this, intzero_add],
      unfold_coes, simp [fin.val], rw ← int.coe_nat_eq_coe_nat_iff,
      have : int.of_nat i % int.of_nat n ≥ (0 : ℤ), by norm_cast,
      rw int.nat_abs_of_nonneg this, repeat { rw int.of_nat_eq_coe },
      rw [← int.coe_nat_mod, int.coe_nat_eq_coe_nat_iff],
      exact nat.mod_eq_of_lt hj
    }
end

section ext

variables {m n : ℕ} {α : Type} {m₁ m₂ : matrix m n α}

theorem ext_iff : m₁.g = m₂.g ↔ m₁ = m₂ :=
  by cases m₁; rcases m₂; simp

@[extensionality] theorem ext : m₁.g = m₂.g → m₁ = m₂ := ext_iff.1

@[extensionality]
lemma m_ext {m₁ m₂ : matrix m n α}
  (h : ∀i j, matrix_at m₁ i j = matrix_at m₂ i j) : m₁ = m₂ :=
begin
  let m₁' := @matrix_of_f m n _ m₁.1.1
    (λx y, abs_data (vec_grid_of_dep_vec_grid m₁.1) ⟨⟨x.1, ⟨_, _⟩⟩, ⟨y.1, ⟨_, _⟩⟩⟩),
  let m₂' := @matrix_of_f m n _ m₂.1.1
    (λx y, abs_data (vec_grid_of_dep_vec_grid m₂.1) ⟨⟨x.1, ⟨_, _⟩⟩, ⟨y.1, ⟨_, _⟩⟩⟩),
  swap 2, { simp [vec_grid_of_dep_vec_grid] },
  swap 2, {
    simp [vec_grid_of_dep_vec_grid, expand_gtr, grid.bl, relative_grid.rows, x.2]
  },
  swap 2, { simp [vec_grid_of_dep_vec_grid] },
  swap 2, {
    simp [vec_grid_of_dep_vec_grid, expand_gtr, grid.bl, relative_grid.cols, y.2]
  },
  swap 2, { simp [vec_grid_of_dep_vec_grid] },
  swap 2, {
    simp [vec_grid_of_dep_vec_grid, expand_gtr, grid.bl, relative_grid.rows, x.2]
  },
  swap 2, { simp [vec_grid_of_dep_vec_grid] },
  swap 2, {
    simp [vec_grid_of_dep_vec_grid, expand_gtr, grid.bl, relative_grid.cols, y.2]
  },
  have heq₁ : m₁ = m₁',
    {
      rcases m₁ with ⟨⟨h, ⟨d, hd⟩⟩⟩,
      simp [m₁', matrix_of_f],
      apply list.ext_le _ _,
        {
          simp [
            length_generate_eq_size, hd, size, relative_grid.rows,
            relative_grid.cols
          ]
        },
        {
          intros k h₁ h₂, rw nth_generate,
          simp [
            abs_data, relative_grid.cols, relpoint_of_gpoint, relative_grid.contents,
            grid.bl, vec_grid_of_dep_vec_grid
          ],
          delta vec_grid_of_dep_vec_grid, simp [vector.nth],
          congr, norm_cast, unfold_coes, simp [fin.val],
          rw [
            ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add,
            int.coe_nat_mul, int.coe_nat_div
          ],
          have : int.of_nat k % int.of_nat n ≥ (0 : ℤ), by norm_cast,
          rw int.nat_abs_of_nonneg this, repeat { rw int.of_nat_eq_coe },
          symmetry, rw [mul_comm, int.mod_add_div]
        }
    },
  rw heq₁ at h,
  have heq₂ : m₂ = m₂',
    {
      rcases m₂ with ⟨⟨h, ⟨d, hd⟩⟩⟩,
      simp [m₂', matrix_of_f],
      apply list.ext_le _ _,
        {
          simp [
            length_generate_eq_size, hd, size, relative_grid.rows,
            relative_grid.cols
          ]
        },
        {
          intros k h₁ h₂, rw nth_generate,
          simp [
            abs_data, relative_grid.cols, relpoint_of_gpoint, relative_grid.contents,
            grid.bl, vec_grid_of_dep_vec_grid
          ],
          delta vec_grid_of_dep_vec_grid, simp [vector.nth],
          congr, norm_cast, unfold_coes, simp [fin.val],
          rw [
            ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add,
            int.coe_nat_mul, int.coe_nat_div
          ],
          have : int.of_nat k % int.of_nat n ≥ (0 : ℤ), by norm_cast,
          rw int.nat_abs_of_nonneg this, repeat { rw int.of_nat_eq_coe },
          symmetry, rw [mul_comm, int.mod_add_div]
        }
    },
  rw heq₂ at h,
  simp [m₁', m₂'] at h,
  delta vec_grid_of_dep_vec_grid at h,
  rcases m₁ with ⟨⟨h₁, ⟨d₁, hd₁⟩⟩⟩, rcases m₂ with ⟨⟨h₂, ⟨d₂, hd₂⟩⟩⟩, simp at *,
  simp [
    abs_data, relpoint_of_gpoint, relative_grid.contents, grid.bl, expand_gtr,
    vector.nth
  ] at h,
  apply list.ext_le _ _,
    {simp [hd₁, hd₂]},
    {
      intros k hk₁ hk₂,
      have eq₁ : k % n < n, by
        apply nat.mod_lt; exact (gt_and_gt_of_mul_gt h₁).2,
      have eq₂ : k / n < m, {
        rw hd₁ at hk₁, rw nat.div_lt_iff_lt_mul, exact hk₁,
        exact (gt_and_gt_of_mul_gt h₁).2
      },
      specialize h ⟨k / n, eq₂⟩ ⟨k % n, eq₁⟩,
      revert h, rw ← option.some_inj, intros h,
      repeat { rw ← list.nth_le_nth at h }, simp at h,
      rw ← option.some_inj, repeat { rw ← list.nth_le_nth },
      have : k % n + k / n * n = k,
        {
          rw [
            mul_comm,
            ← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add, int.coe_nat_mod,
            int.coe_nat_mul, int.coe_nat_div
          ],
          exact int.mod_add_div _ _
        },
      simp [this] at h, exact h
    }
end

end ext

section operations

variables {m n o p : ℕ} {α β γ δ : Type}

open relative_grid grid

lemma matrix_nonempty {m₁ : matrix m n α} : m * n > 0 := m₁.1.1

def matrix_string [has_to_string α] (m : matrix m n α) :=
  grid_str (vec_grid_of_dep_vec_grid m.g)

instance matrix_repr [has_to_string α] : has_repr (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_to_string [has_to_string α] : has_to_string (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_functor : functor (matrix m n) := {
  map := λα β f m, ⟨f <$> m.g⟩
}

instance matrix_functor_law : is_lawful_functor (matrix m n) := {
  id_map := λα ⟨⟨r, c, h⟩⟩, by simp [(<$>), vector.map_id],
  comp_map := λα β γ f h ⟨⟨r, c, h⟩⟩, by simp [(<$>)]
}

def m₁ : matrix 5 2 ℕ :=
  matrix.mk
    (@dep_vec_grid.mk _ 5 2 dec_trivial
                       ⟨[1, 3, 4, 5, 7, 8, 9, 10, 11, 12], dec_trivial⟩)

def m₂ : matrix 2 3 ℕ :=
  matrix.mk
    (@dep_vec_grid.mk _ 2 3 dec_trivial
                      ⟨[2, 2, 2, 2, 2, 2], dec_trivial⟩)

instance [has_add α] : has_add (matrix m n α) := {
  add := λm₁ m₂, ⟨
    @dep_vec_grid.mk _ m n m₁.1.1 (vector.zip_with (+) m₁.1.2 m₂.1.2)
  ⟩
}

def transpose {α} {m n} (m₁ : matrix m n α) : matrix n m α :=
  matrix_of_f (by rw mul_comm; exact m₁.1.1) $ λi j, matrix_at m₁ j i

theorem transpose_transpose_eq_self (A : matrix m n α) :
  transpose (transpose A) = A := by ext; simp [transpose]

end operations

end matrix