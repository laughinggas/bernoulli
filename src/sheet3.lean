import number_theory.bernoulli_polynomials

open finset polynomial power_series
open_locale big_operators nat

-- Bernoulli polynomials multiplication theorem :
-- For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).

theorem exp_ne_constant {R} [ring R] [nontrivial R] [algebra ℚ R] (a : R) : exp R ≠ a • 1 :=
λ h, by simpa using power_series.ext_iff.mp h 1

theorem rescale_ne_constant {R} [comm_semiring R] [no_zero_divisors R]
  (s : power_series R) {a : R} (ha : a ≠ 0) (b : R) (hc : ∀ a : R, s ≠ a • 1) :
  rescale a s ≠ b • 1 := λ h, hc b
begin
  ext (- | t),
  simpa using power_series.ext_iff.mp h 0,
  simpa [ha] using power_series.ext_iff.mp h t.succ
end

theorem bernoulli_generating_function' (t : ℚ) :
  power_series.mk (λ n, polynomial.eval t ((1 / n! : ℚ) • polynomial.bernoulli n)) * (exp ℚ - 1) =
  power_series.X * rescale t (exp ℚ) := bernoulli_generating_function t

lemma function.smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) :
  (λ n : ℕ, a * (f n)) = a • (λ n : ℕ, f n) :=
  funext $ λ n, by simp only [pi.smul_apply, smul_eq_mul]

lemma power_series.mk_smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) : mk (a • f) = a • mk f :=
  power_series.ext $ λ n, by simp only [coeff_mk, pi.smul_apply, power_series.coeff_smul]

lemma rescale_mk {R : Type*} [comm_semiring R] (f : ℕ → R) (a : R) :
  rescale a (mk f) = mk (λ n : ℕ, a^n * (f n)) :=
  power_series.ext $ λ n, by simp only [coeff_rescale, coeff_mk]

lemma power_series.sum_mk {α β} [comm_semiring β] {s : finset α} (f : α → ℕ → β) :
  power_series.mk (λ t, ∑ x in s, f x t) = ∑ x in s, power_series.mk (λ t, f x t) :=
  power_series.ext $ λ n, by simp only [coeff_mk, linear_map.map_sum]

lemma rescale_one' {R : Type*} [comm_semiring R] (f : power_series R) : rescale 1 f = f :=
  by simp only [rescale_one, ring_hom.id_apply]

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
  -- use `bernoulli_generating_function` to change the LHS to `X * e^{k*x} * (e^{k*x} - 1)`
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk,
    -- change `k^{n - 1}` in the RHS to `1/k * k^n`
    have : ∀ n : ℕ, (k : ℚ)^(n - 1 : ℤ) = 1 / k * k^n,
    { intro n,
      rw [zpow_sub₀ hk', mul_comm, mul_div, zpow_one, div_left_inj' hk', mul_one, zpow_coe_nat] },
    simp_rw [this],
    -- use `function.smul` `rescale_mk` to get the power series in terms of `rescale k`
    conv_rhs { congr, congr, congr, funext, rw [mul_comm _ (k ^ j : ℚ), mul_div_assoc, mul_assoc] },
    rw [←power_series.rescale_mk],
    simp_rw [mul_sum],
    rw [power_series.sum_mk, bernoulli_generating_function, mul_comm (k : ℚ) y, rescale_mul,
        ring_hom.comp_apply, mul_assoc, ←map_one (rescale (k : ℚ)), ←map_sub, ←map_mul, mul_sub], 
    nth_rewrite 1 [←rescale_one' (exp ℚ)],
    rw [exp_mul_exp_eq_exp_add, mul_one, map_sub],
    -- want to reduce LHS to X * (rescale k) (exp ℚ)      X * (e^{k(y+1)x} - e^{kyx}) = X * e^{kx}

    -- use `bernoulli_generating_function'` and `rescale_rescale`
    
    --now use `hk` to cancel out `↑k`
     
    -- use `exp_mul_exp_eq_exp_add` and `exp_pow_eq_rescale_exp`
    
    -- use `mul_sum` to extract the constants from the sum, and then apply the GP sum using `geom_sum_mul`
    
    -- almost got the same form, apply `congr_arg2` to deal with the individual cases
    sorry
  }
end
