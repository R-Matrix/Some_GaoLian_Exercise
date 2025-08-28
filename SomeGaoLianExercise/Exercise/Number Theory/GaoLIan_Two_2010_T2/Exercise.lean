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

#eval f 3 4.5

variable {k : ℕ} {r : ℚ} (hr : r = k + 1 / 2)

example : ∃ m n : ℕ, f m r = n := sorry

#check Nat.factorization
#eval Nat.factorization 16 2

#check Nat.factorization_eq_zero_iff
#check Int.ceil_add_natCast


































end section
