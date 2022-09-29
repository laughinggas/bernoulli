import data.polynomial.algebra_map
import data.nat.choose.cast
import number_theory.bernoulli

open_locale big_operators -- so that we can use `∑` instead of `finset.sum`
open_locale nat polynomial -- so that we can use `n!`
open nat finset
open power_series
open polynomial

-- taking A to be a commutative ring and a ℚ-algebra
variables (A : Type*) [comm_ring A] [algebra ℚ A]

/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * bernoulli' n

@[simp] lemma bernoulli_neg_zero : bernoulli_neg 0 = 1 := by simp [bernoulli_neg, bernoulli'_zero]

@[simp] lemma bernoulli_neg_one : bernoulli_neg 1 = -1/2 := by { rw [bernoulli_neg, bernoulli'_one], norm_num }

lemma nat.one_le_of_ne_zero_and_ne_one {n : ℕ} (h0 : n ≠ 0) (h1 : n ≠ 1) : 1 < n :=
begin
  cases n,
  { exfalso,
    apply h0,
    refl },
  contrapose h1,
  push_neg, 
  simp [nat.succ_le_iff] at h1,
  simp [h1]
end

-- bernoulli_neg n = bernoulli' n for all values of n, n ≠ 1
theorem bernoulli_neg_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli_neg n = bernoulli' n :=
begin
  rw bernoulli_neg,
  by_cases h0 : n = 0,
  { rw [h0, bernoulli'_zero],
    norm_num },
  by_cases hn' : odd n,
  -- odd
  { rw bernoulli'_odd_eq_zero hn' _,
    norm_num,
    exact nat.one_le_of_ne_zero_and_ne_one h0 hn },
  -- even
  { have h : (-1 : ℚ) ^ n = 1,
    { rw [odd_iff_not_even, not_not] at hn',
      cases hn' with k h,
      simp [h, ← two_mul, pow_mul] },
    simp [h] }
end

@[simp] theorem sum_bernoulli_neg (n : ℕ) :
  ∑ k in range n, (n.choose k : ℚ) * bernoulli_neg k = if n = 1 then 1 else 0 :=
begin
  -- looked at `sum_bernoulli`
  cases n, { simp },
  cases n, { simp },
  suffices : ∑ i in range n, ↑((n + 2).choose (i + 2)) * bernoulli_neg (i + 2) = n / 2,
  { simp only [this, sum_range_succ', cast_succ, bernoulli_neg_one, bernoulli_neg_zero, choose_one_right,
    mul_one, choose_zero_right, cast_zero, if_false, zero_add, succ_succ_ne_one], ring },
  have f := sum_bernoulli' n.succ.succ,
  simp_rw [sum_range_succ', bernoulli'_one, choose_one_right, cast_succ, ← eq_sub_iff_add_eq] at f,
  convert f,
  { funext x, rw bernoulli_neg_eq_bernoulli'_of_ne_one (succ_ne_zero x ∘ succ.inj) },
  { simp only [one_div, mul_one, bernoulli'_zero, cast_one, choose_zero_right, add_sub_cancel],
    ring }
end