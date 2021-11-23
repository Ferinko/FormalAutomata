-- Random assortment of utilities used throughout the project.

-- Integer (modulo) arithmetic properties.
-- Data structure properties.
-- Auxiliary algorithms and their poperties.

import data.int.basic data.list data.vector tactic.omega tactic.linarith

namespace utils 

open int nat list

lemma gt_and_gt_of_mul_gt {m n : ℕ} (h : m * n > 0) : m > 0 ∧ n > 0 :=
  by simp only [gt_from_lt] at *;
  exact ⟨
    pos_of_mul_pos_right h (nat.zero_le _),
    pos_of_mul_pos_left h (nat.zero_le _)
  ⟩

lemma mul_gt_of_gt_gt {m n : ℕ} (h₁ : m > 0) (h₂ : n > 0) : m * n > 0 :=
  mul_pos h₁ h₂

lemma lt_add_coe_of_gt_zero {x : ℤ} {y : ℕ} (h : y > 0) : x < x + ↑y :=
  lt_add_of_pos_right _ (by simpa [gt_from_lt, h])

lemma lt_of_add_lt {m n k : ℕ} (h : m + n < k) : m < k := by omega

lemma nat_le_dest : ∀ {n m : ℕ}, n < m → ∃ k, nat.succ n + k = m
  | n ._ (less_than_or_equal.refl ._)  := ⟨0, rfl⟩
  | n ._ (@less_than_or_equal.step ._ m h) :=
    match le.dest h with
      | ⟨w, hw⟩ := ⟨succ w, hw ▸ rfl⟩
    end

lemma zip_nil_right {α β : Type} {l : list α} : zip l ([] : list β) = [] :=
  by cases l; refl

lemma zip_nil_iff {α β : Type} (l₁ : list α) (l₂ : list β) :
  list.zip l₁ l₂ = [] ↔ l₁ = [] ∨ l₂ = [] :=
iff.intro (λh, by cases l₁; cases l₂; finish)
          (λh, begin cases h with h₁ h₁; rw h₁;
                     unfold zip zip_with,
                     exact zip_nil_right end)

lemma zip_with_len_l {α β γ : Type*} {l₁ : list α} {l₂ : list β} {f : α → β → γ}
  (h : length l₁ = length l₂) : length (zip_with f l₁ l₂) = length l₁ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {simp [zip_with]},
    {
      cases l₂ with y ys,
        {injection h},
        {simp only [zip_with, length], finish}
    }
end

lemma zip_with_len_r {α β γ : Type*} {l₁ : list α} {l₂ : list β} {f : α → β → γ}
  (h : length l₁ = length l₂) : length (zip_with f l₁ l₂) = length l₂ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {rw ← h, simp [zip_with]},
    {
      cases l₂ with y ys,
        {injection h},
        {simp only [zip_with, length], finish}
    }
end

lemma nat_abs_zero_iff (a b : ℤ) : nat_abs (a - b) = 0 ↔ a = b :=
begin
  split; generalize h : a - b = c, intros h₁,
    {
      cases c; dsimp at h₁, rw h₁ at h,
        {omega},
        {cases h₁}
    },
    {intros h₁, rw [← h, h₁, sub_self], refl}
end

lemma join_empty_of_all_empty {α : Type*} (xs : list (list α)) 
  (h : (∀x, x ∈ xs → x = [])) : join xs = [] :=
begin
  induction xs with x xs ih,
    {refl},
    {
      unfold join,
      have h₁ : x = [], from h _ (by left; refl),
      simp [h₁, nil_append, (ih (λx₁, λh₂, h _ (mem_cons_of_mem _ h₂)))]
    }
end

lemma repeat_more {α : Type} {x : α} {n : ℕ} (h : n ≥ 1) :
  repeat x n = x :: repeat x (n - 1) :=
begin
  cases n,
    {cases h},
    {simp [repeat_succ]}
end

lemma one_le_succ {a : ℕ} : 1 ≤ nat.succ a := by omega

lemma nat_abs_ge_one_of_lt {a b : ℤ} (h : a < b) : nat_abs (b - a) ≥ 1 :=
have h₁ : b - a > 0, from sub_pos_of_lt h,
begin
  simp only [ge_from_le],
  rw [← coe_nat_le, nat_abs_of_nonneg (int.le_of_lt h₁), int.coe_nat_one],
  omega
end

lemma neg_lt_add_one_of_ge_zero (n : ℕ) (a : ℤ) (h : a ≥ 0) : -↑n < a + (1 : ℤ)
  := have h₁ : -↑n ≤ (0 : ℤ), {rw [neg_le, neg_zero], trivial},
     have h₂ : 0 < a + 1, {rw lt_add_one_iff, exact h},
     lt_of_le_of_lt h₁ h₂

lemma sub_one_mul_gt_of_gt_mul_gt {a b : ℕ} (h : a > 1) (h₁ : a * b > 0) :
  (a - 1) * b > 0 :=
begin
  apply mul_pos _ (gt_and_gt_of_mul_gt h₁).2; simp [gt_from_lt] at *,
  rw [← int.coe_nat_lt_coe_nat_iff, int.coe_nat_sub (le_of_lt h), lt_sub],
  simp, norm_cast, exact h
end

section bounded

variables {α : Type} [decidable_linear_order α]

def bounded (a b : α) :=
  {x : α // a ≤ x ∧ x < b}

def is_bounded (a b : α) (y : α) :=
  a ≤ y ∧ y < b

lemma is_bounded_of_bounds {a b y : α} (h : a ≤ y) (h₁ : y < b) :
  is_bounded a b y := and.intro h h₁

instance is_bounded_dec (a b y : α) : decidable (is_bounded a b y) :=
  by simp [is_bounded]; apply_instance

def make_bounded {a b : α} {x : α} (h : is_bounded a b x) : bounded a b :=
  ⟨x, h⟩

def bounded_to_str [φ : has_to_string α] {a b : α} :
  bounded a b → string := λx, to_string x.1

instance bounded_repr {a b : α} [has_to_string α] :
  has_repr (bounded a b) := ⟨bounded_to_str⟩

instance bounded_str (a b : α) [has_to_string α] :
  has_to_string (bounded a b) := ⟨bounded_to_str⟩

instance bounded_to_carrier_coe (a b : α) : has_coe (bounded a b) α :=
  ⟨λx, x.1⟩

instance zbound_dec_eq {a b : α} : decidable_eq (bounded a b)
  | ⟨x, _⟩ ⟨y, _⟩ := by apply_instance

instance coe_bounded {α : Type} {a b : α} [decidable_linear_order α] :
  has_coe (@bounded α _ a b) α := ⟨λx, x.1⟩

lemma positive_bounded {x : ℕ} (a : bounded 0 x) : ↑a ≥ 0 :=
let ⟨a, ⟨l, r⟩⟩ := a in by simpa

lemma bounded_lt {x : ℕ} (a : bounded 0 x) : ↑a < x :=
let ⟨a, ⟨l, r⟩⟩ := a in by simpa

end bounded

structure point := (x : ℤ) (y : ℤ)

private def point_rep : point → string
  | ⟨x, y⟩ := "[" ++ to_string x ++ ", " ++ to_string y ++ "]"

def point_eq (p₁ p₂ : point) := p₁.x = p₂.x ∧ p₁.y = p₂.y

instance dec_eq_p {p₁ p₂} : decidable (point_eq p₁ p₂) :=
  by simp [point_eq]; apply_instance

instance dec_eq_point : decidable_eq point :=
  λ⟨x₁, y₁⟩ ⟨x₂, y₂⟩,
  begin
    by_cases h₁ : x₁ = x₂;
    by_cases h₂ : y₁ = y₂,
      {apply is_true, rw h₁, rw h₂},
      {
        apply is_false,
        rw h₁, intros contra,
        injection contra, contradiction
      },
      {
        apply is_false,
        rw h₂, intros contra,
        injection contra, contradiction
      },
      {
        apply is_false,
        intros contra, injection contra,
        contradiction
      } 
  end

instance : has_to_string point := ⟨point_rep⟩

instance : has_repr point := ⟨point_rep⟩

def left (p₁ p₂ : point) := if p₁.x ≤ p₂.x then p₁ else p₂
def right (p₁ p₂ : point) := if p₁.x ≤ p₂.x then p₂ else p₁
def up (p₁ p₂ : point) := if p₁.y ≤ p₂.y then p₂ else p₁
def down (p₁ p₂ : point) := if p₁.y ≤ p₂.y then p₁ else p₂

def grid_sorted : point → point → Prop
  | ⟨x, y⟩ ⟨x₁, y₁⟩ := x < x₁ ∧ y < y₁

infix `↗` : 50 := grid_sorted

instance {a b : point} : decidable (a ↗ b) :=
  let ⟨x, y⟩ := a in
  let ⟨x₁, y₁⟩ := b in by simp [(↗)]; apply_instance

instance : is_irrefl point grid_sorted := {
  irrefl := λ⟨x, y⟩, by simp [(↗)]
}

instance : is_trans point grid_sorted := {
  trans := λ⟨x, y⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨h, h₁⟩ ⟨h₂, h₃⟩,
             by simp [(↗)] at *; split; linarith
}

instance [c : is_irrefl point grid_sorted]
         [c₁ : is_trans point grid_sorted] :
         is_strict_order point grid_sorted := by constructor; assumption

lemma le_of_zero_le_add_le (a b c : ℤ) (h₁ : 0 ≤ b) (h₂ : a + b ≤ c) : a ≤ c :=
  by omega

lemma zero_lt_one_add {a} : 0 < 1 + a := by omega

lemma grid_bounded_iff {p₁ p₂ : point} : p₁↗p₂ ↔ (p₁.x < p₂.x ∧ p₁.y < p₂.y) :=
  by cases p₁; cases p₂; simp [(↗)]

lemma length_zip_left {α β : Type*} {l₁ : list α} {l₂ : list β}
  (h : length l₁ = length l₂) : length (zip l₁ l₂) = length l₁ :=
  by induction l₁ with l₃h l₃t ih generalizing l₂; cases l₂; finish

lemma not_grid_bounded_iff {p₁ p₂ : point} :
  ¬p₁↗p₂ ↔ (p₂.x ≤ p₁.x ∨ p₂.y ≤ p₁.y) :=
begin
  cases p₁; cases p₂,
  unfold point.x point.y,
  simp [(↗)],
  split; intros h,
  {
    by_cases h₁ : p₁_x < p₂_x,
      {right, exact h h₁},
      {
        rw not_lt_iff_eq_or_lt at h₁, finish
      }
  },
  {intros h₁, cases h; linarith}
end

private lemma abs_nat_lt : ∀{n m : ℤ}, (0 ≤ n) → n < m → nat_abs n < nat_abs m
  | (of_nat n₁) (of_nat n₂) zlen nltm :=
  begin
    dsimp,
    revert n₁, induction n₂ with _ ih; intros; cases n₁,
    {cases nltm},
    {cases nltm},
    {apply zero_lt_succ},
    {
      apply succ_lt_succ (ih _ _ _),
      {
        cases n₁, exact le_refl _,
        rw [of_nat_succ, add_comm], simp
      },
      {
        repeat {rw of_nat_succ at nltm},
        exact lt_of_add_lt_add_right nltm
      }
    }
    -- This proof breaks beta reduction further down the line, ouch.
    -- rw ← int.coe_nat_lt_coe_nat_iff,
    -- have : of_nat n₂ ≥ (0 : ℤ), linarith,
    -- repeat { rw int.nat_abs_of_nonneg }; assumption
  end

def range_weaken_lower_any {a b c : ℤ} (h : c ≤ a) : bounded a b → bounded c b
  | ⟨i, ⟨lbound, rbound⟩⟩ :=
    ⟨i, ⟨le_trans h lbound, rbound⟩⟩

def range_weaken_upper_any {a b c : ℤ} (h : b ≤ c) : bounded a b → bounded a c
  | ⟨i, ⟨lbound, rbound⟩⟩ :=
    ⟨i, ⟨lbound,
        (have h : b < c ∨ b = c, from lt_or_eq_of_le h,
           or.elim h
             (assume h, lt_trans rbound h)
             (by cc))⟩⟩

def range_weaken {a b : ℤ} (h : bounded (a + 1) b) : bounded a b
  := range_weaken_lower_any
       (le_of_zero_le_add_le _ 1 _ dec_trivial (le_refl _)) h

lemma range_weaken_n {a b : ℤ} {c : bounded (a + 1) b} :
  c.1 = (range_weaken c).1 :=
begin
  cases c with c p,
  unfold range_weaken, delta range_weaken_lower_any, simp,
  cases p, dsimp, finish
end

def range : ∀(a b : ℤ), list (bounded a b) 
  | fro to := if h : fro < to
              then ⟨fro, and.intro (le_refl _) h⟩
                   :: list.map range_weaken (range (fro + 1) to)
              else []
  using_well_founded {
    rel_tac := λf args,
      `[exact ⟨
          measure (λ⟨fro, to⟩, nat_abs (to - fro)),
          measure_wf _
        ⟩],
    dec_tac := `[apply abs_nat_lt, {linarith [h]}, {linarith}]
  }

def range_pure : ℤ → ℤ → list ℤ
  | fro to :=  if h : fro < to
               then fro :: range_pure (fro + 1) to else []
  using_well_founded {
    rel_tac := λf args,
      `[exact ⟨
          measure (λ⟨a, b⟩, nat_abs (b - a)),
          measure_wf _
        ⟩],
    dec_tac := `[apply abs_nat_lt, {linarith [h]}, {linarith}]
  }          

lemma range_pure_cons {a b} {x xs} (h : range_pure a b = x :: xs) :
  range_pure (a + 1) b = xs :=
begin
  unfold1 range_pure at h,
  by_cases h₁ : (a < b); simp [h₁] at h; finish
end

lemma range_pure_next {a b} (h : a < b):
  range_pure a b = a :: range_pure (a + 1) b :=
begin
  generalize h₁ : a :: range_pure (a + 1) b = l,
  unfold1 range_pure, simpa [if_pos h]
end

lemma range_pure_bounded {a b : ℤ} :
  ∀{c}, c ∈ range_pure a b → is_bounded a b c :=
assume c,
begin
  generalize h : range_pure a b = l,
  induction l with x xs ih generalizing a b; intros h₁,
    {cases h₁},
    {
      rw mem_cons_iff at h₁,
      cases h₁ with h₁,
        {
          subst h₁,
          unfold1 range_pure at h,
          by_cases h₂ : a < b; simp [h₂] at h,
            {exact ⟨h.1 ▸ le_refl _, h.1 ▸ h₂⟩},
            {contradiction}
        },
        {
          unfold1 range_pure at h,
          by_cases eq : a < b; simp [eq] at h,
            {
              have ih₁ := @ih (a + 1) b h.2 h₁,
              exact ⟨int.le_of_lt (lt_of_add_one_le ih₁.1), ih₁.2⟩
            },
            {contradiction}
        }
    }
end

lemma range_pure_empty_iff {a b} : range_pure a b = [] ↔ (b ≤ a) :=
begin
  split; intros h,
    {
      unfold1 range_pure at h,
      by_cases h₁ : a < b; simp [h₁] at h,
        {contradiction},
        {omega}
    },
    {
      unfold1 range_pure,
      by_cases h₁ : a < b; simp [h₁],
      omega
    }
end

lemma range_pure_same_empty {a} : range_pure a a = [] :=
  range_pure_empty_iff.2 (le_refl _)

lemma in_range_pure_of_bounded {a b} {x}
  (h : is_bounded a b x) : x ∈ range_pure a b :=
begin
  generalize h₃ : range_pure a b = l,
  induction l with y ys ih generalizing a,
    {
      rw range_pure_empty_iff at h₃,
      unfold is_bounded at h, exfalso, omega,
    },
    {
      simp only [is_bounded] at h, rw le_iff_lt_or_eq at h,
      cases h.left with h₁ h₁,
        {
          exact mem_cons_of_mem _
            (@ih (a + 1) ⟨add_one_le_of_lt h₁, h.2⟩ (@range_pure_cons _ _ y _ h₃))
        },
        {
          subst h₁,
          have h₄ : a = y, {
            unfold1 range_pure at h₃, rw if_pos h.2 at h₃, injection h₃
          }, 
          left, cc
        }
    }
end

lemma range_pure_singleton {x} : range_pure x (x + 1) = [x] :=
  by rw [range_pure_next (lt_add_one _), range_pure_empty_iff.2 (le_refl _)]

lemma in_range_iff {a b} {x} : x ∈ range_pure a b ↔ is_bounded a b x :=
  ⟨range_pure_bounded, in_range_pure_of_bounded⟩

def range_pure_m (a b : ℤ) : list ℤ := map (λx : bounded a b, x.1) (range a b)

lemma range_empty_iff {a b : ℤ} : range a b = [] ↔ (b ≤ a) :=
begin
  split; intros h; unfold1 range at *,
  {by_cases h₁ : a < b; simp [h₁] at h; finish},
  {by_cases h₁ : a < b; simp [h₁], omega}
end

lemma range_len_zero_iff (a b : ℤ) : length (range a b) = 0 ↔ b ≤ a :=
begin
  split; intros h,
  {
    unfold1 range at h,
    by_cases h₁ : a < b; simp [h₁] at h; finish
  },
  {simp [range_empty_iff.2 h]}
end

lemma range_length_same_zero (a : ℤ) : length (range a a) = 0 :=
  by unfold1 range; simp [(lt_irrefl _)]

lemma range_length_one (a : ℤ) : length (range a (a + 1)) = 1 :=
begin
  unfold1 range,
  have h : a < a + 1, from lt_add_succ _ _,
  simp [h, range_length_same_zero]
end

lemma range_pure_length_same (a : ℤ) : length (range_pure a a) = 0 :=
  by unfold1 range_pure; simp [(lt_irrefl _)]

lemma range_pure_length_one (a : ℤ) : length (range_pure a (a + 1)) = 1 :=
begin
  unfold1 range_pure,
  have h : a < a + 1, from lt_add_succ _ _,
  simp [h, range_pure_length_same]
end

lemma range_length {a b : ℤ} (h : a ≤ b) :
  length (range a b) = nat_abs (b - a) :=
begin
  generalize h₁ : nat_abs (b - a) = n,
  induction n with n ih generalizing a b,
    {
      rw nat_abs_zero_iff at h₁, rw h₁,
      exact range_length_same_zero _
    },
    {
      have h₂ : a < b,
        {
          rw le_iff_eq_or_lt at h,
          cases h,
            {
              have h : b = a, by cc,
              rw ← nat_abs_zero_iff at h,
              rw h at h₁, cases h₁
            },
            {exact h}
        },
      have h₃ : a + 1 ≤ b, from add_one_le_of_lt h₂,
      have h₄ : nat_abs (b - (a + 1)) = n,
        begin
          rw [← sub_sub, ← int.coe_nat_eq_coe_nat_iff],
          have h₅ : b - a - 1 ≥ (0 : ℤ), by linarith,
          rw [nat_abs_of_nonneg h₅,
              ← @add_right_cancel_iff _ _ (1 : ℤ) _ _,
              sub_add_cancel],
          have h₆ : b - a ≥ (0 : ℤ), by linarith,
          rw [← int.coe_nat_eq_coe_nat_iff, nat_abs_of_nonneg h₆] at h₁,
          exact h₁
        end,
      have ih := ih h₃ h₄,
      unfold1 range at ih,
      rw le_iff_eq_or_lt at h₃,
      cases h₃,
        {
          have h₇ : ¬a + 1 < b,
            by rw ← h₃; intros contra; exact absurd contra (lt_irrefl _),  
          simp [h₇] at ih,
          rw [← ih, ← h₃, range_length_one]
        },
        {
          simp [h₃] at ih, unfold1 range,
          simp [h₂], unfold1 range,
          simp [h₃],
          rw [← ih, ← one_add]
        }
    }
end

lemma range_length_pure {a b : ℤ} (h : a ≤ b) :
  length (range_pure a b) = nat_abs (b - a) := 
begin
  generalize h₁ : nat_abs (b - a) = n,
  induction n with n ih generalizing a b,
    {
      rw nat_abs_zero_iff at h₁, rw h₁,
      exact range_pure_length_same _
    },
    {
      have h₂ : a < b,
        begin
          rw le_iff_eq_or_lt at h,
          cases h,
            {
              have h : b = a, by cc,
              rw ← nat_abs_zero_iff at h,
              rw h at h₁, cases h₁
            },
            {exact h}
        end, clear h,
      have h₃ : a + 1 ≤ b, from add_one_le_of_lt h₂,
      have h₄ : nat_abs (b - (a + 1)) = n,
        begin
          rw [← sub_sub, ← int.coe_nat_eq_coe_nat_iff],
          have h₅ : b - a - 1 ≥ (0 : ℤ), by linarith,
          rw [nat_abs_of_nonneg h₅, ← @add_right_cancel_iff _ _ (1 : ℤ) _ _,
              sub_add_cancel],
          have h₆ : b - a ≥ (0 : ℤ), by linarith,
          rw [← int.coe_nat_eq_coe_nat_iff, nat_abs_of_nonneg h₆] at h₁,
          exact h₁
        end,
      have ih := ih h₃ h₄,
      unfold1 range_pure at ih,
      rw le_iff_eq_or_lt at h₃,
      cases h₃,
        {
          have h₇ : ¬a + 1 < b,
            by rw ← h₃; intros contra; exact absurd contra (lt_irrefl _),
          simp [h₇] at ih,
          rw [← ih, ← h₃, range_pure_length_one]
        },
        {
          simp [h₃] at ih, unfold1 range_pure,
          simp [h₂], unfold1 range_pure,
          simp [h₃], rw [← ih, ← one_add]
        }
    }
end

open list function

def empty_list {α : Type} (l : list α) := [] = l

lemma not_empty_of_len {α : Type} {l : list α}
  (h : length l > 0) : ¬empty_list l :=
begin
  simp [empty_list], cases l, {cases h}, {trivial}
end

lemma empty_list_eq_ex {α : Type} {l : list α} (h : ¬empty_list l) :
  ∃(x : α) (xs : list α), l = x :: xs :=
begin
  cases l with lh lt,
    {unfold empty_list at h, contradiction},
    {use lh, use lt}
end

instance decidable_empty_list {α : Type} : ∀l : list α,
  decidable (empty_list l)
  | [] := is_true rfl
  | (x :: _) := is_false (by simp [empty_list])

theorem nonempty_nil_eq_false {α : Type} : ¬(empty_list (@nil α)) ↔ false :=
  by simp [empty_list]

def head1 {α : Type} (l : list α) (h : ¬empty_list l) :=
  match l, h with
    | [], p := by rw nonempty_nil_eq_false at p; contradiction
    | (x :: _), _ := x
  end

lemma head1_nonempty_eq_head {α : Type} (l : list α) (h : ¬empty_list l) :
  head1 l h = @head _ {
    default := begin
                 unfold empty_list at h,
                 cases l with e _, 
                   {contradiction},
                   {exact e}
               end
  } l :=
begin
  cases l, unfold empty_list at h, contradiction,
  unfold head1, refl
end

def foldr1 {α : Type} (f : α → α → α) (l : list α) (h : ¬empty_list l) : α :=
  match l, h with
    | [], p := by rw nonempty_nil_eq_false at p; contradiction
    | (x :: xs), _ := foldr f x xs
  end

lemma foldr1_nonempty_eq_foldr {α : Type} (f : α → α → α) (l : list α)
  (h : ¬empty_list l) : foldr1 f l h = list.foldr f (head1 l h) (tail l) :=
begin
  cases l,
    {rw nonempty_nil_eq_false at h, contradiction},
    {unfold foldr1 head1 tail}
end

def min_element {α : Type} [decidable_linear_order α]
  (l : list α) (h : ¬empty_list l) := foldr1 min l h

def max_element {α : Type} [decidable_linear_order α]
  (l : list α) (h : ¬empty_list l) := foldr1 max l h

lemma foldr_swap {α : Type*}
  (f : α → α → α) (h : is_commutative _ f) (h₁ : is_associative _ f)
  {x y : α} {xs : list α} :
  foldr f x (y :: xs) = foldr f y (x :: xs) :=
have comm : ∀a b, f a b = f b a, by finish,
have assoc : ∀a b c, f a (f b c) = f (f a b) c, by finish,
list.rec_on xs
  (comm _ _) 
  (assume x₁ xs₁ ih,
   by dsimp at *;
      rw [assoc, comm y, ← assoc, ih, assoc, comm x₁, ← assoc])

lemma le_min_elem_of_all {α : Type*} [decidable_linear_order α]
  (l : list α) (b : α) (h : ¬empty_list l) :
  (∀x, x ∈ l → b ≤ x) → b ≤ min_element l h :=
assume h₁,
begin
  induction l with y ys ih,
    {unfold empty_list at h, contradiction},
    {
      unfold min_element foldr1,
      cases ys with ysh yst,
        {simp [h₁]},
        {
          have ih := ih (by unfold empty_list; intros ok; cases ok)
                        (by intros; apply h₁; right; simp [(∈)] at a; exact a),  
          unfold min_element foldr1 at ih,
          rw foldr_swap min ⟨min_comm⟩ ⟨min_assoc⟩,
          dsimp at *, rw le_min_iff,
          exact ⟨by simp [h₁], by assumption⟩
        }
    }
end

lemma max_le_elem_of_all {α : Type*} [decidable_linear_order α]
  (l : list α) (b : α) (h : ¬empty_list l) :
  (∀x, x ∈ l → x ≤ b) → max_element l h ≤ b :=
assume h₁,
begin
  induction l with y ys ih,
    {unfold empty_list at h, contradiction},
    {
      unfold max_element foldr1,
      cases ys with ysh yst,
        {simp [h₁]},
        {
          have ih := ih (by unfold empty_list; intros ok; cases ok)
                        (by intros; apply h₁; right; simp [(∈)] at a; exact a),
          unfold max_element foldr1 at ih,
          rw foldr_swap max ⟨max_comm⟩ ⟨max_assoc⟩,
          dsimp at *, rw max_le_iff,
          exact ⟨by simp [h₁], by assumption⟩
        }
    }
end

lemma min_le_max {α : Type*} [decidable_linear_order α] {a b c : α}
  (H : b ≤ c) : min a b ≤ max a c :=
begin
  unfold min max,
  by_cases h : a ≤ b; simp [h];
    by_cases h₁ : a ≤ c; simp [h₁],
  {exact H},
  {rw not_le at h, exact le_of_lt h}
end

lemma min_elem_le_max_elem {α : Type*} [decidable_linear_order α] (l : list α)
  (h : ¬empty_list l) : min_element l h ≤ max_element l h :=
begin
  unfold min_element max_element,
  cases l with x xs,
    {unfold empty_list at h, contradiction},
    {
      unfold foldr1,
      induction xs with y ys; dsimp,
        {refl},
        {
          have h₁ : ¬empty_list (x :: ys),
            by unfold empty_list; intros; contradiction,
          exact min_le_max (xs_ih h₁)
        }
    }
end

lemma max_elem_sub_min_elem_nonneg 
  {l : list ℤ} (h : ¬empty_list l) : max_element l h - min_element l h ≥ 0 :=
begin
  unfold min_element max_element, repeat { rw foldr1_nonempty_eq_foldr },
  rw head1_nonempty_eq_head,
  induction l with x xs ih,
    {unfold empty_list at h, contradiction},
    {
      by_cases h₁ : empty_list xs,
        {unfold empty_list at h₁, subst h₁, simp},
        {
          simp, cases xs with y ys,
            {unfold empty_list at h₁, contradiction},
            {
              specialize ih h₁, simp [-sub_eq_add_neg] at ih,
              rw foldr_swap max ⟨max_comm⟩ ⟨max_assoc⟩,
              rw foldr_swap min ⟨min_comm⟩ ⟨min_assoc⟩,
              simp, rw ← sub_eq_add_neg, unfold min max,
              by_cases h₂ : x ≤ foldr max y ys;
                by_cases h₃ : x ≤ foldr min y ys; simp [h₂, h₃]; linarith,
            }
        }
    }
end

lemma map_empty_iff_l_empty {α β : Type} {f : α → β} {l : list α} :
  empty_list (map f l) ↔ empty_list l :=
  by split; intros h; cases l; try {finish <|> simp [empty_list]}

lemma unzip_one {α β : Type} (l : α) (r : β) (xs : list (α × β)) :
  unzip ((l, r) :: xs) = ((l :: (unzip xs).fst), r :: (unzip xs).snd) :=
  by simp [unzip]; cases (unzip xs); simp [unzip]

lemma unzip_fst_empty_iff_l_empty {α β : Type} (l : list (α × β)) :
  empty_list (unzip l).fst ↔ empty_list l :=
begin
  split; intros h; cases l with lh lt; try {finish};
  simp [empty_list, unzip] at *,
  cases lh, rw unzip_one at h,
  contradiction
end

lemma unzip_snd_empty_iff_l_empty {α β : Type} (l : list (α × β)) :
  empty_list (unzip l).snd ↔ empty_list l :=
begin
  split; intros h; cases l with lh lt; try {finish};
  simp [empty_list, unzip] at *,
  cases lh, rw unzip_one at h,
  contradiction
end

lemma pair_in_zip_l {α β} {a b} {l₁ : list α} {l₂ : list β}
  (h : (a, b) ∈ zip l₁ l₂) : a ∈ l₁ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {simp [zip, zip_with] at h, contradiction},
    {cases l₂ with y ys; finish}
end

lemma pair_in_zip_r {α β} {a b} {l₁ : list α} {l₂ : list β}
  (h : (a, b) ∈ zip l₁ l₂) : b ∈ l₂ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {simp [zip, zip_with] at h, contradiction},
    {cases l₂ with y ys; finish}
end

def decidable_uncurry {α β : Type*} {f : α → β → Prop} {x : α × β}
  (h : decidable (f x.fst x.snd)) : decidable (uncurry f x) :=
begin
  resetI,
  cases x, unfold_projs at *,
  simp [uncurry], exact h
end

lemma filter_forall {α : Type*} {P : α → Prop} [decidable_pred P] (xs : list α)
  (x : α) (h₁ : x ∈ filter P xs) : P x :=
begin
  induction xs with x₁ xs₁ ih; simp [filter] at h₁,
    {contradiction},
    {
      by_cases h₂ : (P x₁); simp [h₂] at h₁,
        {cases h₁,
           {cc},
           {exact h₁.right}},
        {exact h₁.right}
    }
end

lemma nonempty_filter_ex {α : Type*} {xs : list α} {p : α → Prop}
  [decidable_pred p] (h : ¬empty_list (filter p xs)) :
  ∃x, x ∈ xs ∧ p x :=
begin
  induction xs with x₁ xs₁ ih,
    {dsimp at h, unfold empty_list at h, contradiction},
    {
      by_cases h₁ : p x₁,
        {use x₁, finish},
        {
          simp [filter, h₁] at h,
          cases ih h with x₂ px₂,
          use x₂, exact ⟨by right; exact px₂.1, px₂.2⟩
        }
    }
end

def conv {α : Type*} (f : α → Type*) {a b : α} : a = b → f a → f b :=
  assume h₁ h₂, by rw ← h₁; exact h₂

def list_iso {α : Type*} [decidable_eq α] : list α → list α → bool
  | []        []        := tt
  | (x :: xs) (y :: ys) := band (x = y) (list_iso xs ys)
  | _         _         := ff

lemma list_iso_refl {α : Type*} [decidable_eq α] {l : list α} :
  list_iso l l :=
  by induction l; simp [list_iso]; assumption

lemma list_iso_nil_l {α : Type*} [decidable_eq α] {l : list α}
  : list_iso nil l ↔ l = nil := by cases l; simp [list_iso, list_iso_refl]

lemma list_iso_nil_r {α : Type*} [decidable_eq α] {l : list α}
  : list_iso l nil ↔ l = nil := by cases l; simp [list_iso, list_iso_refl]

lemma list_iso_symm {α : Type*} [decidable_eq α] {l₁ l₂ : list α}
  (h : list_iso l₁ l₂) : list_iso l₂ l₁ :=
begin
  induction l₁ with x xs ih generalizing l₂; cases l₂ with y ys; try {assumption},
  simp [list_iso], simp [list_iso] at h,
  cases h with h₁ h₂; simp*
end

lemma list_iso_trans {α : Type*} [decidable_eq α] {l₁ l₂ l₃ : list α}
  (h : list_iso l₁ l₂) (h₁ : list_iso l₂ l₃) : list_iso l₁ l₃ :=
begin
  induction l₁ with x xs ih generalizing l₂ l₃; cases l₃ with y ys,
    {exact list_iso_refl},
    {
      rw list_iso_nil_l at h, rw h at h₁,
      rw list_iso_nil_l at h₁, cases h₁
    },
    {rw list_iso_nil_r at h₁, rw h₁ at h, exact h},
    {
      simp [list_iso],
      cases l₂ with z zs,
        {rw list_iso_nil_r at h, cases h},
        {
          simp [list_iso] at h h₁,
          exact ⟨by cc, ih h.2 h₁.2⟩
        }
    }
end

lemma list_iso_hd {α : Type*} [decidable_eq α] {x} {y} {xs ys : list α}
  (h : list_iso (x :: xs) (y :: ys)) : x = y :=
  by simp [list_iso] at h; exact h.left

lemma list_iso_tl {α : Type*} [decidable_eq α] {x} {y} {xs ys : list α}
  (h : list_iso (x :: xs) (y :: ys)) : list_iso xs ys :=
  by simp [list_iso] at h; exact h.right

lemma list_iso_iff {α : Type*} [decidable_eq α] {l₁ l₂ : list α} :
  list_iso l₁ l₂ ↔ l₁ = l₂ :=
begin
  split; intros h,
    { 
      induction l₁ with x xs ih generalizing l₂,
        {
          cases l₂ with y ys,
            {refl},
            {rw list_iso_nil_l at h, cases h}
        },
        {
          cases l₂ with y ys, 
            {rw list_iso_nil_r at h, cases h},
            {
              have h₁ : x = y, from list_iso_hd h,
              congr, {exact h₁}, {exact ih (list_iso_tl h)}
            }
        }
    },
    {rw h, exact list_iso_refl}
end

def iterate {α : Type*} (f : α → α) (x : α) : ℕ → α
  | 0 := x
  | (k + 1) := f (iterate k)

lemma iterate_zero {α : Type*} {f : α → α} {x : α} : iterate f x 0 = x := rfl

lemma iterate_one {α : Type*} {n : ℕ} {f : α → α} {x : α} :
  iterate f x (n + 1) = f (iterate f x n) := rfl

lemma iterate_iterate_add {α : Type*} {f : α → α} {x : α} {m n : ℕ} :
  iterate f (iterate f x m) n = iterate f x (m + n) :=
begin
  induction n with n ih,
    {simp [iterate_zero, add_zero]},
    {
      rw [
        succ_eq_add_one, iterate_one,
        ih, ← add_assoc, iterate_one
      ]
    }
end

lemma iterate_iterate_mul {α : Type*} {f : α → α} {x : α} {m n : ℕ} :
  iterate (λy, iterate f y m) x n = iterate f x (m * n) :=
begin
  induction n with n ih generalizing x,
    {simp [iterate_zero]},
    {
      simp [iterate_one, mul_succ],
      rw [ih, add_comm, iterate_iterate_add.symm]
    }
end

lemma iterate_id_of_x {α : Type*} {f : α → α} {x : α} {n : ℕ}
  (h : f x = x) : iterate f x n = x :=
begin
  induction n with n ih,
    {simp [iterate_zero]},
    {simp [iterate_one, ih, h]}
end

lemma one_mod_many {n} : 1 % nat.succ (nat.succ n) = 1 :=
begin
  cases n with n,
    {refl},
    {rw [nat.mod_def, if_neg], safe, omega}
end

lemma mod_mod_succ {m n} (h : (m + 1) % n ≠ 0) : m % n + 1 = (m + 1) % n :=
begin
  have h₁ := nat.mod_add_div m n,
  generalize s₁ : m % n = r,
  generalize s₂ : m / n = q,
  rw [s₁, s₂] at h₁,
  have h₂ : 0 ≤ r, from nat.zero_le _,
  have h₄ : n = 0 ∨ n ≠ 0, from classical.em _,
  cases h₄,
    {subst h₄, rw ← h₁, simp},
    {
      have h₅ : r < n,
        {
          rw ← s₁, apply nat.mod_lt,
          cases n,
            {contradiction},
            {clear h₁ h₂ h₄ h s₁ s₂, omega}
        },
      simp [h₁.symm],
      by_cases h₆ : r + 1 < n,
        {
          rw [← add_assoc, add_comm, nat.add_mul_mod_self_left],
          rw add_comm at h₆, rw nat.mod_eq_of_lt h₆
        },
        {
          rw not_lt_iff_eq_or_lt at h₆,
          cases h₆,
            {
              rw [
                ← h₆, ← h₁, add_comm, ← add_assoc,
                add_comm 1, add_mod_left, ← h₆,
                ← zero_add ((r + 1) * q),
                nat.add_mul_mod_self_left,
                nat.zero_mod
              ] at h,
              contradiction
            },
            {linarith}
        }
    }
end

lemma periode_cycle {α : Type*} {f : α → α} {x : α} {m n : ℕ}
  (h : iterate f x n = x) : iterate f x m = iterate f x (m % n) :=
begin
  have : m = m % n + n * (m / n), from (nat.mod_add_div m n).symm,
  generalize h₁ : iterate f x (m % n) = rhs,
  rw [this, add_comm, ← iterate_iterate_add, ← iterate_iterate_mul],
  subst h₁, congr, rwa iterate_id_of_x
end

lemma repeat_bounded {α : Type*} {a : α} {b} :
  ∀{x}, x ∈ list.repeat a b → x = a :=
assume x h,
begin
  induction b with b ih,
    {cases h},
    {
      simp at h,
      cases h, {assumption}, {exact ih h}
    }
end

lemma update_nth_pres_len {α : Type} (l : list α) {n} {x} :
  length (update_nth l n x) = length l :=
begin
  induction l with y ys ih generalizing n,
    {refl},
    {cases n with n; unfold update_nth; simp [ih]}
end

lemma zip_fst {α β : Type} {x : α × β}
  {l₁ : list α} {l₂ : list β} (h : x ∈ zip l₁ l₂) : x.fst ∈ l₁ :=
begin
  induction l₁ with y ys ih generalizing l₂,
    {rw zip_nil_left at h, cases h},
    {
      cases l₂,
        {rw zip_nil_right at h, cases h},
        {
          rw [zip_cons_cons, mem_cons_eq] at h,
          cases h,
            {rw h, dsimp, left, refl},
            {right, exact ih h}
        }
    }
end

lemma filter_first_irrel {α β : Type} {x}
  {l₁ : list α} {l₂ : list β}
  {P : β → Prop} [decidable_pred P] {R : α → Prop} :
  x ∈ filter (P ∘ prod.snd) (zip l₁ l₂) → (∀y ∈ l₁, R y) → R x.fst :=
assume h₁ h₂,
begin
  apply h₂, revert h₁,
  generalize h₃ : filter (P ∘ prod.snd) (zip l₁ l₂) = l,
  intros,
  have h₄ : l ⊆ zip l₁ l₂, rw ← h₃, apply filter_subset,
  rw subset_def at h₄,
  have h₅ : x ∈ zip l₁ l₂, from h₄ h₁,
  exact zip_fst h₅
end

lemma unzip_singleton {α β : Type} {x : α} {y : β} : (unzip [(x, y)]).fst = [x] :=
  by simp [unzip]

lemma unzip1_fst {α β : Type} {x} {y} {l : list (α × β)} :
  (unzip ((x, y) :: l)).fst = x :: (unzip l).fst := by simp [unzip_cons]

lemma unzip_subset {α β : Type} {l₁ : list α} {l₂ : list β}
  {P : α × β → Prop} [decidable_pred P] :
  (unzip (filter P (zip l₁ l₂))).fst ⊆ l₁ :=
assume x h,
begin
  induction l₁ with y ys ih generalizing l₂,
    {
      rw [zip_nil_left, filter_nil, unzip_nil] at h,
      cases h
    },
    {
      cases l₂ with y₂ ys₂,
      {
        rw [zip_nil_right, filter_nil, unzip_nil] at h,
        cases h,
      },
      {
        rw zip_cons_cons at h,
        by_cases h₂ : P (y, y₂),
        {
          rw [filter_cons_of_pos, unzip1_fst, mem_cons_eq] at h,
          cases h; try { finish }, assumption
        },
        {
          rw filter_cons_of_neg _ h₂ at h,
          right, exact ih h
        }
      }
    }
end

lemma zunzip_filter_first_irrel {α β : Type} {x}
  {l₁ : list α} {l₂ : list β}
  {P : α × β → Prop} [decidable_pred P] {R : α → Prop} :
  x ∈ (unzip (filter P (zip l₁ l₂))).fst → (∀y ∈ l₁, R y) → R x :=
assume h₁ h₂,
begin
  apply h₂, revert h₁,
  generalize h₃ : (unzip (filter P (zip l₁ l₂))).fst = l,
  intros,
  have h₄ : (unzip (filter P (zip l₁ l₂))).fst ⊆ l₁, from unzip_subset,
  rw subset_def at h₄,
  apply h₄, rw h₃,
  exact h₁
end

lemma in_zip_of {x} {y} {l₁} {l₂} :
  point.mk x y ∈ map (function.uncurry point.mk) (zip l₁ l₂) →
  x ∈ l₁ ∧ y ∈ l₂ :=
assume h,
begin  
  split; {
    induction l₁ with z zs ih generalizing l₂; cases l₂ with l₂h l₂t,
      {rw zip_nil_left at h, dsimp at h, cases h},
      {rw zip_nil_left at h, dsimp at h, cases h},
      {rw zip_nil_right at h, dsimp at h, cases h},
      {
        dsimp at h,
        rw mem_cons_iff at h,
        cases h,
          {simp [uncurry] at h, left, try {exact h.1}; try { exact h.2} },
          {right, exact ih h}
      }
    }
end

lemma point_in_zip_prod_iff {x} {y} {l₁} {l₂} :
  point.mk x y ∈ map (function.uncurry point.mk) (zip l₁ l₂) ↔
  (x, y) ∈ zip l₁ l₂ :=
begin
  split; intros h; {
    induction l₁ with l₁h l₁t ih generalizing l₂; cases l₂ with l₂h l₂t;
      try {rw zip_nil_left at h; cases h},
      {rw zip_nil_right at h, cases h},
      {
        dsimp at h, rw mem_cons_iff at h,
        cases h,
          {dsimp, left, cases h, refl},
          {right, apply ih h}
      }
  }
end
lemma repeat_empty_iff {α : Type} {x : α} {n} :
  repeat x n = [] ↔ n = 0 :=
begin
  split; intros h,
    {cases n, {refl}, {dsimp at h, cases h}},
    {subst h, refl}
end

lemma repeat_sub_of_cons {α : Type} {y : α} {n} {x} {xs} (h : repeat y n = x :: xs) :
  repeat y (n - 1) = xs :=
begin
  cases n; dsimp at h, {cases h}, {injection h}
end

lemma point_in_zip_repeat_right
  {α β : Type} {n} {x : α} {y : β} {l₁ : list α} {l₂}
  (h₁ : length l₁ = length l₂) (h₂ : list.repeat y n = l₂) (h₃ : x ∈ l₁) :
  (x, y) ∈ zip l₁ l₂ :=
begin
  induction l₁ with l₁h l₁t ih generalizing l₂ n; cases l₂ with l₂h l₂t,
    {cases h₃},
    {cases h₃},
    {rw repeat_empty_iff at h₂, cases h₁},
    {      
      rw mem_cons_iff at h₃,
      cases h₃,
        {
          subst h₃, rw zip_cons_cons, left,
          have : l₂h = y,
            {
              cases n, contradiction,
              dsimp at h₂, injection h₂,
              cc
            },
          cc
        },
        {
          dsimp, right,
          apply @ih h₃ _ (n - 1),
          repeat { rw length_cons at h₁ },
          injection h₁,
          exact repeat_sub_of_cons h₂
        }
    }
end

lemma nat_abs_nonneg {x} : 0 ≤ int.nat_abs x :=
  by cases x; simp; apply nat.zero_le

lemma maps_f_ext_eq {α β : Type} {xs : list α} {f g : α → β}
  (h : ∀x ∈ xs, f x = g x) : map f xs = map g xs :=
begin
  induction xs with y ys ih,
    {refl},
    {
      dsimp,
      have : f y = g y, from h _ (mem_cons_self _ _), rw this,
      exact congr_arg _ (ih (λ_ h₁, h _ (mem_cons_of_mem _ h₁)))
    }
end

lemma nth_le_in_grid {α : Type} {n} {x} {l : list α} {p}
  (h : x = nth_le l n p) : x ∈ l :=
begin
  induction n with n ih generalizing l; cases l with y ys; dsimp at h,
    {cases h, cases h, cases p},
    {rw h, left, refl},
    {cases p},
    {right, exact ih h}
end

lemma nth_le_zero {α : Type} {x} {xs : list α} {p}
  : nth_le (x :: xs) 0 p = x := rfl

lemma attach_empty_iff {α : Type} {l : list α} :
  empty_list (attach l) ↔ empty_list l :=
begin
  split; intros h;
    {
      induction l with x xs ih,
        {constructor},
        {
          simp [attach, empty_list] at h,
          contradiction
        }
    }
end

lemma not_map_empty_of_not_empty {α β : Type} {l : list α} {f : α → β}
  (h : ¬empty_list l) : ¬empty_list (map f l) :=
  assume contra, by simp [empty_list] at h; cases l with x xs; contradiction

lemma not_join_empty_of_not_empty {α : Type} {l : list (list α)} :
  empty_list (join l) → (empty_list l ∨ ∀xs ∈ l, empty_list xs) :=
assume h,
begin
  induction l with y ys ih,
    {left, constructor},
    {
      have h₁ : y = [], by simp [empty_list] at h; exact h.1,
      rw h₁, right, intros h₂ h₃, rw mem_cons_eq at h₃,
      cases h₃,
        {rw h₃, constructor},
        {
          rw h₁ at h, dsimp at h,
          have ih := ih h,
          simp [empty_list] at ih,
          cases ih with ih ih,
            {rw ← ih at h₃, cases h₃},
            {exact ih _ h₃}
        }
    }
end

lemma not_empty_cons {α : Type} {x} {xs : list α} : ¬empty_list (x :: xs) :=
assume contra,
  by simp [empty_list] at contra; contradiction

lemma abs_minus_plus {a b : ℤ}
  (h : a > b) : nat_abs (a - b) - 1 = nat_abs (a - (b + 1)) :=
begin
  have : a - (b + 1) ≥ 0, by simp; omega,
  rw [← int.coe_nat_eq_coe_nat_iff, nat_abs_of_nonneg this],
  clear this,
  have h₁ : a - b ≥ 0, by omega,
  have h₂ : 1 ≤ nat_abs (a - b),
    by rw [← int.coe_nat_le_coe_nat_iff, nat_abs_of_nonneg]; omega,
  rw [int.coe_nat_sub h₂, nat_abs_of_nonneg h₁],
  simp
end

lemma count_eq_iff {α : Type} [decidable_eq α] {l₁ l₂ : list α}
  (h : l₁ = l₂) {x} : list.count x l₁ = list.count x l₂ :=
  by cases l₁ with y ys; cases l₂ with z za; finish

lemma list_empty_iff_len {α : Type} {l : list α} : l = [] ↔ length l = 0 :=
  by split; intros h; cases l with x xs; finish  

lemma map_eq_repeat {ps} {r} :
  map point.y ps = repeat r (length ps) →
  ∀p : point, p ∈ ps → p.y = r :=
begin
  generalize h : length ps = n,
  intros h₁ p h₂,
  induction n with n ih generalizing ps,
    {
      rw length_eq_zero at h, rw h at h₂,
      cases h₂
    },
    {
      cases ps with psh pst, cases h₂,
      have h₃ : length pst = n, by dsimp at h; injection h,
      finish
    }
end

lemma mul_one_less {a b : ℤ} : a * b = a + (b - 1) * a := by ring

lemma mul_one_less_n {a b : ℕ} (h : b > 0) : a * b = a + (b - 1) * a :=
begin
  simp [gt_from_lt] at h,
  rw [nat.mul_sub_right_distrib, ← nat.add_sub_assoc],
    {simp [mul_comm]},
    {
      simp, cases b,
        {cases h},
        {rw succ_mul, exact nat.le_add_left _ _}
    }
end

lemma nonneg_of_lt {x₁ x₂ : ℤ} (h : x₁ < x₂) : x₂ - x₁ ≥ 0 :=
  by omega

lemma nth_split {α : Type} {l₁ l₂ : list α} {n} (h : n < length l₁):
  nth (l₁ ++ l₂) n = nth l₁ n :=
begin
  induction n with n ih generalizing l₁ l₂,
    {
      cases l₁, {simp, cases h}, {refl}
    },
    {
      cases l₁ with x xs,
        {simp, cases h},
        {
          simp at *, apply ih,
          rw [add_comm, add_one] at h,
          exact lt_of_succ_lt_succ h
        }
    }
end

lemma nth_split_second {α : Type} {l₁ l₂ : list α} {n} (h : ¬n < length l₁):
  nth (l₁ ++ l₂) n = nth l₂ (n - length l₁) :=
begin
  induction n with n ih generalizing l₁ l₂,
    {cases l₁, simp, simp at h, contradiction},
    {
      cases l₁ with x xs,
        {simp},
        {
          simp, simp at h, rw nat.one_add at h,
          have h : length xs ≤ n, from le_of_succ_le_succ h,
          specialize @ih xs l₂ (not_lt.2 h),
          rw [ih, succ_eq_add_one, add_comm, nat.add_sub_add_left]
        }
    }
end

lemma zip_with_nil_r {α β γ : Type}
  {l : list α} {f : α → β → γ} : zip_with f l nil = nil :=
  by cases l with x xs; refl; unfold zip_with

lemma zip_with_const_eq_map {α β γ : Type}
  {l₁ : list α} {l₂ : list β} {f : β → γ}
  (h : length l₁ = length l₂) :
  zip_with (λ_ y, f y) l₁ l₂ = map f l₂ :=
begin
  induction l₂ with x xs ih generalizing l₁,
    {
      cases l₁ with y ys,
        {simp [zip_with]},
        {rw zip_with_nil_r, simp}
    },
    {
      cases l₁ with y ys,
        {cases h},
        {
          unfold zip_with map, simp at h,
          exact congr_arg _ (ih h)
        }
    }
end

lemma length_zip_with {α β γ : Type}
  {l₁ : list α} {l₂ : list β} {f : α → β → γ} (h : length l₁ = length l₂) :
  length (zip_with f l₁ l₂) = length l₁ := 
begin
  induction l₁ with x xs ih generalizing l₂; cases l₂;
    try {unfold length at h, rw ← succ_eq_add_one at h, cases h},
    {refl},
    {simp [zip_with], apply ih, injection h}
end

lemma mod_add_div_coe {i c : ℕ} :
  int.nat_abs(↑i % ↑c) + int.nat_abs(↑i / ↑c) * c = i :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_add, int.coe_nat_mul],
  have : ↑i % ↑c ≥ (0 : ℤ), by simp [ge_from_le]; linarith,
  repeat { rw nat_abs_of_nonneg; try { assumption } }, 
  rw [mul_comm, int.mod_add_div]
end

namespace vector

@[simp]
lemma map_id {α : Type} {n} {v : vector α n} : vector.map id v = v :=
  by cases v; simp [vector.map]

@[simp]
lemma map_map {α β γ} {n} {g : β → γ} {f : α → β} {v : vector α n} :
  vector.map g (vector.map f v) = vector.map (g ∘ f) v :=
  by cases v; simp [vector.map]

@[simp]
lemma nth_map {α β} {m n} {f : α → β} {v : vector α m} :
  vector.nth (vector.map f v) n = f (vector.nth v n) :=
by cases v with v h; simp [vector.map, vector.nth]

def zip_with {α β γ : Type} {n} (f : α → β → γ)
  (v₁ : vector α n) (v₂ : vector β n) : vector γ n :=
  ⟨list.zip_with f v₁.to_list v₂.to_list, by simp [length_zip_with]⟩

lemma to_list_inj {α : Type} {n} {v₁ v₂ : vector α n}
  (h : vector.to_list v₁ = vector.to_list v₂) : v₁ = v₂ :=
  by cases v₁; cases v₂; simp at *; exact h

end vector

end utils