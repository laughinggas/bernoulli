import data.polynomial.algebra_map
import data.nat.choose.cast
import number_theory.bernoulli
-- where do these files come from?

open_locale big_operators -- so that we can use `∑` instead of `finset.sum`
open_locale nat polynomial -- so that we can use `n!`
open nat finset
open power_series
open polynomial

-- taking A to be a commutative ring and a ℚ-algebra
variables (A : Type*) [comm_ring A] [algebra ℚ A]

-- Go check the definition of `bernoulli'`!
/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * bernoulli' n

-- What does the `simp` tag do?
@[simp] lemma bernoulli_neg_zero : bernoulli_neg 0 = 1 :=
by rw [bernoulli_neg, pow_zero, bernoulli'_zero, mul_one]

-- Try to solve this with and without `norm_num`
@[simp] lemma bernoulli_neg_one : bernoulli_neg 1 = -1/2 :=
by rw [bernoulli_neg, pow_one, bernoulli'_one, mul_div, mul_one]

-- What does the statement say? Write a docstring
theorem bernoulli_neg_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli_neg n = bernoulli' n :=
begin
  rcases eq_or_ne n 0 with rfl | hn₀,
  { rw [bernoulli_neg_zero, bernoulli'_zero] },
  cases n.even_or_odd with h h,
  { rw [bernoulli_neg, (neg_one_pow_eq_one_iff_even (show (-1 : ℚ) ≠ 1, by norm_num)).mpr h,
        one_mul] },
  { replace hn := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn₀, hn⟩,
    simp_rw [bernoulli_neg, bernoulli'_odd_eq_zero h hn, mul_zero] }
end

lemma bernoulli'_eq : ∀ n, bernoulli' n = (if n = 1 then 1 else 0) + bernoulli_neg n
| 0     := by simp
| 1     := by norm_num
| (n+2) := by simp [bernoulli_neg_eq_bernoulli'_of_ne_one]

lemma one_sub_half : (1 : ℚ) - 1 / 2 = 1 / 2 := by norm_num

-- Challenge!
-- What does the statement say? Write a docstring ; how do you get the `∑` symbol?
@[simp] theorem sum_bernoulli_neg (n : ℕ) :
  ∑ k in range n, (n.choose k : ℚ) * bernoulli_neg k = if n = 1 then 1 else 0 :=
begin
  cases n,
  { rw [range_zero, sum_empty, if_neg], rintro ⟨⟩ },
  cases n,
  { rw [range_one, sum_singleton, bernoulli_neg_zero, mul_one,
        choose_zero_right, nat.cast_one, if_pos rfl] },
  rw [if_neg n.succ_succ_ne_one],
  set q := n.succ.succ with hq,
  suffices : ∑ x in range q, (q.choose x : ℚ) * bernoulli' x = q,
  { have key := sum_sdiff_eq_sub (singleton_subset_iff.mpr $ mem_range.mpr n.one_lt_succ_succ),
    rw [this, sum_singleton, choose_one_right, bernoulli'_one, ←mul_one_sub, one_sub_half] at key,
    rw [←sum_sdiff (singleton_subset_iff.mpr $ mem_range.mpr n.one_lt_succ_succ), sum_singleton,
        choose_one_right, bernoulli_neg_one, neg_div, mul_neg, ←key, ←sub_eq_add_neg, sub_eq_zero],
    refine sum_congr rfl (λ x hx, _),
    congr',
    rw [mem_sdiff, mem_singleton] at hx,
    exact bernoulli_neg_eq_bernoulli'_of_ne_one hx.2 },
  apply sum_bernoulli',
end

/-

`elan` is annoying...

-/
