import number_theory.bernoulli_polynomials

open finset polynomial power_series
open_locale big_operators nat

--local notation `𝔹` := polynomial.bernoulli
--local notation `psm` := power_series.mk

-- Today's aim:   to prove this
-- Bernoulli polynomials multiplication theorem :
--  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).

-- nontrivial R comes for free but I cba
theorem exp_ne_constant {R} [ring R] [nontrivial R] [algebra ℚ R] (a : R) : exp R ≠ a • 1 :=
λ h, by simpa using power_series.ext_iff.mp h 1

theorem rescale_ne_constant {R} [comm_semiring R] [no_zero_divisors R]
  (s : power_series R) {a : R} (ha : a ≠ 0) (b : R) (hc : ∀ a : R, s ≠ a • 1) :
  rescale a s ≠ b • 1 := λ h, hc b
begin
  ext (-|t),
  simpa using power_series.ext_iff.mp h 0,
  simpa [ha] using power_series.ext_iff.mp h t.succ
end

/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`, using eval instead of aeval. -/
theorem bernoulli_generating_function' (t : ℚ) :
  power_series.mk (λ n, polynomial.aeval t ((1 / n! : ℚ) • polynomial.bernoulli n)) * (exp ℚ - 1) = power_series.X * rescale t (exp ℚ) :=
begin
  -- hint : how different is it from `bernoulli_generating_function`?
  sorry,
end

lemma function.smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) :
  (λ n : ℕ, a * (f n)) = a • (λ n : ℕ, f n) := sorry

lemma power_series.mk_smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) : mk (a • f) = a • mk f := sorry

lemma rescale_mk {R : Type*} [comm_semiring R] (f : ℕ → R) (a : R) :
  rescale a (mk f) = mk (λ n : ℕ, a^n * (f n)) := sorry

lemma rescale_comp_eq_mul {R : Type*} [comm_semiring R] (f : power_series R) (a b : R) : rescale b (rescale a f) = rescale (a * b) f := sorry

theorem bernoulli_eval_mul (m : ℕ) {k : ℕ} (hk : k ≠ 0) (y : ℚ) : (polynomial.bernoulli m).eval ((k : ℚ) * y) = k^(m - 1 : ℤ) * ∑ i in finset.range k, (polynomial.bernoulli m).eval (y + i / k) :=
begin
  suffices : power_series.mk (λ j, ((k : ℚ) ^ (j - 1 : ℤ) / j!) * ∑ i in range k, (polynomial.bernoulli m).eval (y + i / k)) * (exp ℚ - 1) * (rescale ↑k (exp ℚ) - 1) =
  power_series.mk (λ j, aeval (↑k * y) ((1 / j! : ℚ) • bernoulli j)) * (exp ℚ - 1) * (rescale ↑k (exp ℚ) - 1),
  { replace := mul_right_cancel₀ _ (mul_right_cancel₀ _ this),
    have hm : (m! : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero,
    replace := power_series.ext_iff.mp this m,
    simp only [coeff_mk, one_div, coe_aeval_eq_eval, eval_smul,
               algebra.id.smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hm] at this,
    rw [←this, ←mul_assoc (m! : ℚ), ←mul_div_assoc, mul_div_cancel_left _ hm],
    all_goals { rw sub_ne_zero },
    { convert exp_ne_constant (1 : ℚ),
      simp },
    { convert rescale_ne_constant _ _ _ _,
      exact (one_smul _ 1).symm,
      apply_instance,
      exact_mod_cast hk,
      exact exp_ne_constant } },
  { symmetry, 
    --use `bernoulli_generating_function` to change the LHS to `X * e^{k*x} * (e^{k*x} - 1)`

    have : ∀ n : ℕ, (k : ℚ)^(n - 1 : ℤ) = 1 / k * k^n,
    { intro n, sorry, },
    -- change `k^{n - 1}` in the RHS to `1/k * k^n` using `conv_rhs` or `simp_rw`
    
    -- use `function.smul` `rescale_mk` to get the power series in terms of `rescale k`
    
    -- take `(rescale k) (exp ℚ - 1)` inside the sum in the RHS
    
    -- use `ring_hom.map_mul` to combine the `rescale k` inside the sum in the RHS into a single one (you will need `conv_rhs`)
    
    -- use `bernoulli_generating_function'` and `rescale_comp_eq_mul`
    
    --now use `hk` to cancel out `↑k`
     
    -- use `exp_mul_exp_eq_exp_add` and `exp_pow_eq_rescale_exp`
    
    -- use `mul_sum` to extract the constants from the sum, and then apply the GP sum using `geom_sum_mul`
    
    -- almost got the same form, apply `congr_arg2` to deal with the individual cases
    
    { -- this is a power series, use `power_series.ext`
      apply power_series.ext (λ n, _), { apply_instance, },
      -- use `coeff_rescale` and `power_series.coeff_X`
      
      -- break into cases n = 1 and n ≠ 1; use `if_pos` and `if_neg` to deal with `ite`
      
    { sorry, },
    { -- use properties of `ring_hom` and `exp_pow_eq_rescale_exp`
      sorry, }, },
end