import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Finsupp.Basic

import SomeGaoLianExercise


/-
# 2014 年高中联赛b $\cdot$ 二试

## 第三题

设整数 $k\ge 2$ , $a,b $ 是非负整数, 且 $a + b $ 是一个奇数. 若方程 $a ^ k x - b ^ k y = a - b$ 有整数解 $x, y$, 其中 $0 < |x - y| \le 2$, 求证 :

$|a - b|$ 是某个整数的 $k$ 次幂.


---

## 解析

设 $(a, b) = d$, 且设 $a = da_1, b=db_1$, 则 $(a_1, b_1) = 1$.

由 $a ^ k x - b ^ k y = a - b$  得

$$d ^ {k - 1 } (a_ 1 ^ k x -  b _ 1 ^ k y) = a_1 - b_1, (1) $$

所以 $d^{k-1}\mid a_1 - b_1.$

注意到 (1) 可形变为 $d ^{k-1}a_1^k(x-y) + d^{k-1}(a^k-b^k)y = a_1 - b_1.$

因为 $a_1 - b_1 \mid a_1^k - b_1 ^k$, 所以 $a-1 -b_1 \mid d^{k-1}a_1^k(x-y).$

因为 $0 < |x - y| \le 2$, 且由  $a+b$ 是奇数知 $a-1-b_1$ 是奇数, 所以 $(a_1-b_1, x-y) = 1$.

又 $(a_1-b-1, a_1 ^k) = 1$, 所以 $a-1 - b_1 \mid d^{k-1}.$

这样 , $|a_1 - b_1 = d^{k - 1}|$, 所以 $|a - b|= d|a_1 - b_1| = d^k$ 是整数的 $k$ 次幂.
-/



section

variable (a b : ℤ) (k : ℕ) (hanz : a ≠ 0) (hbnz : b ≠ 0) (abOdd : (a + b)%2 = 1) (hk : k ≥ 2)
          (P : ∃ x y :  ℤ, a ^ k * x - b ^ k *  y = a - b ∧ 0 < |x - y| ∧ |x - y| ≤ 2)

example : ∃ n : ℤ , |a - b| = n ^ k :=
    sorry

#check sub_dvd_pow_sub_pow
#check Int.gcd


theorem GL2014BT3 (hanz : a ≠ 0) (hbnz : b ≠ 0) (abOdd : (a + b)%2 = 1) (hk : k ≥ 2)
          (P : ∃ x y :  ℤ, a ^ k * x - b ^ k *  y = a - b ∧ 0 < |x - y| ∧ |x - y| ≤ 2):
              ∃ n : ℤ , |a - b| = n ^ k := by
  sorry





end section
