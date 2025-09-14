import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Basic

import SomeGaoLianExercise

/-!
# 2025 年高中联赛 $\cdot$ 二试(A卷)

## 第二题

设 $m, n, k$ 都是正整数, $m \ge 2$, 且 $n \ge k \ge 2$.

实数 $x_1 \ge x_2 \ge \cdots \ge x_n \ge 0$, 满足以下两个条件:

1. $x_1 ^ m + x_2 ^ m + \cdots + x _ n ^ m \ge 1$.

2. $x_1 + x_2 + \cdots + x_n \le k$.

证明 : $x_1 + x_2 + \cdots + x_k \ge 1$

---

## 答案

**反证法**. 假设 $x_1 + x_2 + \cdots + x_k < 1$, 我们有

$$1 > x_1 \ge x_2 \ge \cdots \ge x_k \ge 0.$$

设 $x_k = u$, 则 $u \le \dfrac{x_1 + x_2 + \cdots + x_k}{k} < \dfrac 1k$, 又 $m \ge 2$, 故

$$\sum _{i = k+1} ^ n x_i ^m \le \sum _{i = k+1} ^ n x_i ^ 2 \le \sum _{i = k+1} ^ n x_k x_i= u \sum_{i = k+1}^n x_i ,$$

结合两个条件知

$$
\sum _{i = 1}^k x_i ^ m \ge 1 - \sum _{i= k+1}^n x_i^m \ge 1 - u \sum _{i= k+1} ^ n x_i \ge 1 - u \left(k - \sum_{i = 1} ^ k x_i \right)
$$

利用 $x_i ^ m \le x_i ^ 2$ 及 $x_i - u \ge 0 (1 \le i \le k)$, 得

$$
\begin{align*}
    1 - uk &\le \sum_{i = 1}^k x_i ^m - u\sum _{i = 1}^k x_i \le \sum_{i = 1}^k x_i ^2 - u\sum _{i = 1}^k x_i = \sum _{i = 1} ^ k x_i (x_i - u)\\ &\le \sum _{i = 1} ^k (x_i - u) = \sum _{i =1}^k x_i -uk
\end{align*}
$$

这与假设 $x_1 + x_2 + \cdots + x_k < 1$ 矛盾!

因此原命题成立. $\square$

-/



section GLExercise

def x_ : ℕ → ℝ := sorry

variable (n k m : ℕ) (u : ℝ)
variable (hn : 2 ≤ n)
variable (hm : 2 ≤ m)
variable (hk : 2 ≤ k)
variable (hkn : k ≤ n)
variable (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i)
variable (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
variable (hx1 : 1 ≤ ∑ i ∈ Finset.range n, (x_ i) ^ m)
variable (hx2 : ∑ i ∈ Finset.range n, x_ i ≤ k)
variable (xku : x_ (k - 1) = u)


example : 1 ≤ ∑ i ∈ Finset.range k , x_ i :=
  sorry

#check Finset.sum_insert
#check Finset.sum_erase_add
#check Finset.sum_range_add
#check Finset.smul_sum

lemma xk_isMin (xku : x_ (k - 1) = u) (hkn : k ≤ n) (hk : 2 ≤ k)
              (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i) :
          ∀ i : ℕ, 0 ≤ i ∧ i ≤ k - 1 → 0 ≤ x_ i - u := by
  rintro i ⟨hi1, hi2⟩
  rw[←xku]; simp
  apply hx_mono
  constructor
  · simp; refine lt_of_lt_of_le ?_ hkn
    apply (Nat.lt_iff_le_pred (by linarith)).mpr hi2
  · simp; apply Nat.lt_of_succ_le; simp
    rw[Nat.sub_add_cancel]; exact hkn; linarith
  exact hi2

lemma xk_isMax (xku : x_ (k - 1) = u) (hkn : k ≤ n) (hk : 2 ≤ k)
              (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i) :
           ∀ i : ℕ, k ≤ i ∧ i ≤ n - 1 → x_ i ≤ u := by
  rintro i ⟨hi1, hi2⟩
  rw[←xku]; apply hx_mono
  constructor
  · simp; refine lt_of_lt_of_le ?_ hkn
    apply Nat.lt_of_succ_le; simp
    rw[Nat.sub_add_cancel]; linarith
  · simp; apply (Nat.lt_iff_le_pred (by linarith)).mpr hi2
  omega

lemma hx_le_one (hkn : k ≤ n) (hk : 2 ≤ k) (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
            (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i) (hx0 : ∑ i ∈ Finset.range k, x_ i < 1) :
          ∀ i, i ∈ Finset.range n → x_ i < 1 := by
  have hik : ∀ i, i ∈ Finset.range k → x_ i < 1 := by
    intro i hi
    by_contra! h
    rw[←Finset.sum_erase_add _ x_ hi] at hx0
    have : 1 ≤ ∑ x ∈ (Finset.range k).erase i, x_ x + x_ i := by
      have : 0 ≤ ∑ x ∈ (Finset.range k).erase i, x_ x := by
        apply Finset.sum_nonneg
        intro j hj
        apply hx_nonneg; simp at hj; simp
        linarith
      linarith
    linarith
  have := hik 0 (by simp; linarith)
  intro i hi; apply lt_of_le_of_lt ?_ this
  apply (hx_mono 0 i (by simp; exact ⟨by linarith, by simp at hi; apply hi⟩))
  simp

lemma ineq_0 (hm : 2 ≤ m) (hx_le_one : ∀ i, i ∈ Finset.range n → x_ i < 1)
                (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i) :
          ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ m ≤ ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  have : x_ (i + k) < 1 := by apply hx_le_one; simp at *; omega
  refine pow_le_pow_of_le_one ?_ ?_ hm
  apply hx_nonneg; simp at *; omega
  apply le_of_lt this

lemma ineq_0' (hm : 2 ≤ m) (hx_le_one : ∀ i, i ∈ Finset.range n → x_ i < 1)
                (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i) (hkn : k ≤ n) :
          ∑ i ∈ Finset.range k, (x_ i) ^ m ≤ ∑ i ∈ Finset.range k, (x_ i) ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  have : x_ i < 1 := by apply hx_le_one; simp at *; linarith
  refine pow_le_pow_of_le_one ?_ ?_ hm
  apply hx_nonneg; simp at *; omega
  apply le_of_lt this

lemma ineq_1 (hm : 2 ≤ m) (hx_le_one : ∀ i, i ∈ Finset.range n → x_ i < 1) (xku : x_ (k - 1) = u)
            (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
                (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i) :
          ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ m ≤ u * ∑ i ∈ Finset.range (n - k), x_ (i + k) := by
  apply le_trans (ineq_0 n k m hm hx_le_one hx_nonneg) ?_
  rw[←smul_eq_mul, Finset.smul_sum]; simp only [smul_eq_mul]
  apply Finset.sum_le_sum
  intro i hi; rw[pow_two, ←xku]
  have : 0 ≤ x_ (i + k) := by
    apply hx_nonneg
    simp at *; omega
  have : x_ (i + k) ≤ x_ (k - 1) := by
    apply hx_mono (k-1) (i+k)
    constructor
    · simp at *; omega
    · simp at *; omega
    simp at *; omega
  nlinarith

lemma ineq_2 (hk : 2 ≤ k) (hkn : k ≤ n) (hm : 2 ≤ m) (xku : x_ (k - 1) = u)
          (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
          (hx_le_one : ∀ i, i ∈ Finset.range n → x_ i < 1) (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i)
          (ineq1 : ∑ i ∈ Finset.range (n - k), (x_ (i + k)) ^ m ≤ u * ∑ i ∈ Finset.range (n - k), x_ (i + k))
          (hx1 : 1 ≤ ∑ i ∈ Finset.range n, (x_ i) ^ m) (hx2 : ∑ i ∈ Finset.range n, x_ i ≤ k) :
        1 - u * (k - ∑ i ∈ Finset.range k, x_ i) ≤ ∑ i ∈ Finset.range k, (x_ i) ^ m := by
  have : n = k + (n - k) := by omega
  rw[this, Finset.sum_range_add] at hx1
  have i1 : 1 - ∑ i ∈ Finset.range (n - k), x_ (i + k) ^ m ≤ ∑ i ∈ Finset.range k, x_ i ^ m := by simp[add_comm]; linarith
  have i2 : 1 - u * ∑ i ∈ Finset.range (n - k), x_ (i + k) ≤ 1 - ∑ i ∈ Finset.range (n - k), x_ (i + k) ^ m := by
    have ineq_1 := ineq_1 _ _ _ _ hm hx_le_one xku hx_mono hx_nonneg
    linarith
  have i3 : 1 - u * (k - ∑ i ∈ Finset.range k, x_ i) ≤ 1 - u * ∑ i ∈ Finset.range (n - k), x_ (i + k) := by
    have etmp : k - ∑ i ∈ Finset.range k, x_ i ≥ ∑ i ∈ Finset.range (n - k), x_ (k + i) := by
      rw[this, Finset.sum_range_add] at hx2
      linarith
    have u_nonneg : 0 ≤ u := by rw[←xku]; apply hx_nonneg (k - 1); simp; omega
    gcongr; simp[add_comm]; linarith
  linarith

lemma ineq_3 (hk : 2 ≤ k) (hkn : k ≤ n) (hx0 : ∑ i ∈ Finset.range k, x_ i < 1)
          (ineq0' : ∑ i ∈ Finset.range k, (x_ i) ^ m ≤ ∑ i ∈ Finset.range k, (x_ i) ^ 2)
          (xk_isMin : ∀ i : ℕ, 0 ≤ i ∧ i ≤ k - 1 → 0 ≤ x_ i - u) (hx_le_one : ∀ i, i ∈ Finset.range n → x_ i < 1)
          (ineq2 : 1 - u * (k - ∑ i ∈ Finset.range k, x_ i) ≤ ∑ i ∈ Finset.range k, (x_ i) ^ m) :
      1 - u * k ≤ (∑ i ∈ Finset.range k, x_ i) - u * k := by
  have i1 : 1 - u * k ≤ ∑ i ∈ Finset.range k, (x_ i) ^ m - u * ∑ i ∈ Finset.range k, (x_ i) := by
    linarith
  have i2 : ∑ i ∈ Finset.range k, (x_ i) ^ m - u * ∑ i ∈ Finset.range k, (x_ i) ≤
        ∑ i ∈ Finset.range k, (x_ i) ^ 2 - u * ∑ i ∈ Finset.range k, (x_ i) := by
    linarith
  have e3 : ∑ i ∈ Finset.range k, (x_ i) ^ 2 - u * ∑ i ∈ Finset.range k, (x_ i) =
        ∑ i ∈ Finset.range k, x_ i * (x_ i - u) := by
    rw[←smul_eq_mul, Finset.smul_sum, ←Finset.sum_sub_distrib]
    simp only [smul_eq_mul, pow_two, ←sub_mul, mul_comm]
  have i4 : ∑ i ∈ Finset.range k, x_ i * (x_ i - u) ≤ ∑ i ∈ Finset.range k, (x_ i - u) := by
    apply Finset.sum_le_sum; intro i hi
    have t1 := by apply xk_isMin i; simp at *; omega
    have t2 := by apply hx_le_one i; simp at *; omega
    nlinarith
  have e5 : ∑ i ∈ Finset.range k, (x_ i - u) = (∑ i ∈ Finset.range k, x_ i) - u * k := by
    rw[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    simp; linarith
  linarith


theorem GL2025AT2 (_hn : 2 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) (hkn : k ≤ n) (xku : x_ (k - 1) = u)
          (hx_nonneg : ∀ i ∈ Finset.range n, 0 ≤ x_ i) (hx_mono : ∀ i j, i ∈ Finset.range n ∧ j ∈ Finset.range n → i ≤ j → x_ j ≤ x_ i)
          (hx1 : 1 ≤ ∑ i ∈ Finset.range n, (x_ i) ^ m ) (hx2 : ∑ i ∈ Finset.range n, x_ i ≤ k) :
      1 ≤ ∑ i ∈ Finset.range k , x_ i := by
  by_contra! hx0
  have xk_isMin := xk_isMin n k u xku hkn hk hx_mono
  have xk_isMax := xk_isMax n k u xku hkn hk hx_mono
  have hx_le_one := hx_le_one n k hkn hk hx_mono hx_nonneg hx0
  have ineq0 := ineq_0 n k m hm hx_le_one hx_nonneg
  have ineq0' := ineq_0' n k m hm hx_le_one hx_nonneg hkn
  have ineq1 := ineq_1 n k m u hm hx_le_one xku hx_mono hx_nonneg
  have ineq2 := ineq_2 n k m u hk hkn hm xku hx_mono hx_le_one hx_nonneg ineq1 hx1 hx2
  have ineq3 := ineq_3 n k m u hk hkn hx0 ineq0' xk_isMin hx_le_one ineq2
  linarith

end GLExercise
