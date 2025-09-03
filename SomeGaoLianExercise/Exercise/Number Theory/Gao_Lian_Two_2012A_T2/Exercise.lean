import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Finsupp.Basic

import SomeGaoLianExercise

/-
# 2012 年高中联赛A $\cdot$ 二试

## 第二题

求证 : 集合 $A = \{ 2, 2^2, \cdots , 2 ^ n, \cdots \}$ 满足

+ 对每个 $a \in A$, 及 $b \in \mathbb{N}_+ $ , 若 $b < 2a - 1 $, 则 $b(b + 1)$ 一定不是 $2a$ 的倍数;

+ 对每个 $a \in  \bar A$ ($\bar A$ 表示 $A$ 在 $\mathbb N_+$ 中的补集), 且 $a \ne 1$,
  必定存在 $b \in \mathbb N_+, b< 2a-1 $, 使得 $b(b+1)$ 是 $2a$ 的倍数.


---

## 解析

1. 若 $2a \mid b (b + 1)$ , 则由 $2a$ 是 2 的幂且 $(b, b+1) = 1$ 知, $2a \mid b$ 或 $2a \mid b + 1$
   这与 $1 \le b \le 2a - 1$ 矛盾 !

1. 当 $a \in \bar A$ 且 $a \ne 1$ 知, 可设 $a = 2 ^ k m$, 其中 $k$ 是非负整数, $m$ 是大于 1 的奇数
   则 $2a = 2 ^{k+1} m$.
   因为 $(2 ^{k+1}, m) = 1$, 所以由中国剩余定理, 同余方程组
   $$\begin{cases}
        x \equiv 0 (\mod 2 ^{k + 1})\\
        x \equiv -1 (\mod m)
   \end{cases}$$
   在区间 $(0, 2 ^{k + 1})$ 内有解 $x = b$. 容易验证, $b$ 即满足要求. $\square$
-/



section

def A : Set ℕ :=
  {n | ∃ k : ℕ , n = 2 ^ (k + 1) }

variable (a : ℕ)

example (b : ℕ) (ha : a ∈ A) (hbge : 1 ≤ b) (hblt : b < 2 * a - 1) : ¬ (2 * a ∣ b * (b + 1)) :=
  sorry

example (haA : ¬ a ∈ A) (ha : 2 ≤ a) : ∃ b : ℕ, 1 ≤ b ∧ b < 2 * a - 1 ∧ 2 * a ∣ b * (b + 1) :=
  sorry

#check Nat.Coprime.pow_left
#check Nat.Prime.coprime_iff_not_dvd
#check Nat.Coprime.dvd_mul_left
#check Nat.not_dvd_ord_compl
#check Nat.ordProj_mul_ordCompl_eq_self
#check Nat.ordCompl_pos
#check Nat.chineseRemainder

theorem GL2012AT2_1 {a b : ℕ} (ha : a ∈ A) (hbge : 1 ≤ b) (hblt : b < 2 * a - 1) :
            ¬ (2 * a ∣ b * (b + 1)) := by
  sorry

theorem GL2012AT2_2 {a : ℕ} (haA : ¬ a ∈ A) (ha : 2 ≤ a) :
            ∃ b : ℕ, 1 ≤ b ∧ b < 2 * a - 1 ∧ 2 * a ∣ b * (b + 1) := by
  sorry





end section
