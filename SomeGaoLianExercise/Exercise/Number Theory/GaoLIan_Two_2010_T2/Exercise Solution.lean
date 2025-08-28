import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

import SomeGaoLIanExercise

/-
---------------------------------------------------------------------------------------
    # 2010 年高中联赛 $\cdot$ 二试

    ## 第二题

    设 $k$ 是正整数, $r = k + \dfrac 12$,
    记 $f^{(1)}(r)= f(r) = r \lceil r \rceil $, $f ^ {(l)}(r) = f(f^{(l-1)}(r)), l \ge 2 $.
    求证 : 存在正整数 $m$, 使得 $f^{(m)}(r) $ 是一个整数.
    这里$\lceil x \rceil$ 表示不小于实数 $x$ 的最小整数.

    ---

    ## 解析

    记 $v_2(k) = v$

    我们对 $v$ 归纳证明, 当 $m = v + 1$ 时, $f^{(m)}(r)$ 是整数.

    当 $v = 0 $ 时, $k$ 是奇数, 所以
    $$f(r) = (k  + \frac 12) \lceil k + \frac 12 \rceil = (k+\frac 12 ) (k + 1)$$
    是整数.

    假设命题对 $v-1 (v \ge 1)$ 成立, 来看 $v$ 时的情形.

    因为 $k$ 是偶数, 所以
    $$f(r)= (k + \frac 12)\lceil k + \frac 12 \rceil
    = (k + \frac 12)(k + 1) = k ^ 2 + \frac 32 k + \frac 12 = k' + \frac 12 $$
    其中 $k' = k ^ 2 + \frac 32 k$

    因为 $v_2(k ^ 2) = 2v, v_2(\frac 32 k) = v - 1 $, 所以 $v_2(k') = v-1  $.
    由归纳假设, $f^{(v)}(k' + \frac 12) $ 是整数, 所以 $f^{(v + 1)}(r) $ 是整数

    归纳证毕. $\square$
---------------------------------------------------------------------------------------
-/

section

def f : Nat → ℚ → ℚ := fun
  | .zero, r => r * Int.ceil r
  | n + 1, r => f n (f 0 r)
#eval f 2 4.5

variable {k : ℕ} {r : ℚ} (hr : r = k + 1 / 2) (hk : k ≠ 0)

example : ∃ m n : ℕ, f m r = n := sorry

#check Nat.factorization
#eval Nat.factorization 16 2

#check Nat.factorization_eq_zero_iff
#check Int.ceil_add_natCast


theorem GL2010T2 {k : ℕ} {r : ℚ} (hr : r = k + 1 / 2) (hk : k ≠ 0) : ∃ m n : ℕ, f m r = n := by
  match h : k.factorization 2 with
  | 0 =>
    use 0
    unfold f
    rw [hr, add_comm, Int.ceil_add_natCast]; norm_num; rw[add_mul]
    have := (Nat.factorization_eq_zero_iff k 2).mp h
    rcases this with (h1 | h2 | h3)
    · trivial
    · rw[Nat.two_dvd_ne_zero, ←Nat.odd_iff] at h2; rcases h2 with ⟨m, rfl⟩
      rw[add_comm 1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_assoc, mul_add]; norm_num; simp
      use m + 1 + (2 * m + 1) * (2 * m + 2)
      simp
    · trivial
  | v + 1 =>
    have k_dvd : 2 ∣ k := by apply Nat.dvd_of_factorization_pos (by linarith)
    have mul_k_dvd : 2 ∣ 3 * k := by
      exact Nat.dvd_mul_left_of_dvd k_dvd 3
    have gknez : (k ^ 2 + 3 * k / 2) ≠ 0 := by
      apply ne_of_gt; apply add_pos
      apply sq_pos_of_ne_zero hk; apply Nat.div_pos;
      apply Nat.le_of_dvd; simp; apply Nat.pos_of_ne_zero hk; apply mul_k_dvd; norm_num

    ----- 说明终止条件, 也是归纳的地方  -----
    have is_vsub1 : (k ^ 2 + 3 * k / 2).factorization 2 = v := by
      have : k ^ 2 + 3 * k / 2 = k * (2 * k + 3) / 2 := by
        have : 2 ∣ k * (2 * k + 3) := by apply Nat.dvd_mul_right_of_dvd k_dvd (2 * k + 3)
        ring_nf; omega
      rw[this, mul_comm, Nat.mul_div_assoc _ k_dvd, Nat.factorization_mul, Nat.factorization_div k_dvd]
      simp; have : ¬ 2 ∣ 2 * k + 3 := by norm_num;
      rw[Nat.factorization_eq_zero_of_not_dvd this, h]; norm_num; omega; omega

    -----  这里关键是调用, 最后需要说明终止条件  --------
    have key := GL2010T2 (r := (k ^ 2 + 3 * k / 2 : ℕ) + 1 / 2) (by norm_num) (gknez)
    rcases key with ⟨m, n, hmn⟩
    use m + 1, n
    unfold f
    have key2 : (k ^ 2 + 3 * k / 2) + 1 / 2 = f 0 r := by
      rw[hr, f, Rat.add_comm k, Int.ceil_add_natCast]; norm_num; ring
    have hmn_cast : (k ^ 2 + 3 * k / 2 : ℕ) + 1 / 2 = ((k : ℚ) ^ 2 + 3 * (k : ℚ) / 2 + 1 / 2) := by
      norm_cast
    rwa[hmn_cast, key2] at hmn

    termination_by k.factorization 2   ---- `说明终止条件 `






end section
