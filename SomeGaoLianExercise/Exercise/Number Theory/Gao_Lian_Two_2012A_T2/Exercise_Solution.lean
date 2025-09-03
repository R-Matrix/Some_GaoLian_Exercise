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
  intro h
  have bcoprime : b.Coprime (b + 1) := by simp
  rcases ha with ⟨k, ha⟩
  by_cases hb : 2 ∣ b
  · have : ¬ 2 ∣ b + 1 := by omega
    have : Nat.Coprime (2 * a) (b + 1) := by
      have temp : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by nth_rw 1 [←pow_one 2, ←pow_add]; norm_num; linarith
      rw[ha, temp]
      apply Nat.Coprime.pow_left
      apply (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr this
    have :  2 * a ∣ b := (Nat.Coprime.dvd_mul_right this).mp h
    have := Nat.le_of_dvd (by linarith) this
    omega
  · have : Nat.Coprime (2 * a) b := by
      have temp : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by nth_rw 1 [←pow_one 2, ←pow_add]; norm_num; linarith
      rw[ha, temp]
      apply Nat.Coprime.pow_left
      apply (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hb
    have :  2 * a ∣ b + 1 := (Nat.Coprime.dvd_mul_left this).mp h
    have := Nat.le_of_dvd (by linarith) this
    omega


-- lemma resa : ∃ t r : ℕ, 1 < r ∧ r % 2 = 1 ∧ a = 2 ^ t * r := by
--       use Nat.factorization a 2, a / (2 ^ (Nat.factorization a 2))
--       constructor
--       · apply lt_iff_le_and_ne.mpr
--         constructor
--         · apply (Nat.one_le_div_iff (by positivity)).mpr
--           apply Nat.ordProj_le
--           linarith
--         · by_contra! e
--           have e : 2 ^ a.factorization 2 = a := by
--             apply Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd _ _) e.symm
--           apply haA (a.factorization 2 -1)
--           rw[Nat.sub_add_cancel]; exact e.symm
--           have : 2 ∣ a := by omega
--           have := (Nat.factorization_prime_le_iff_dvd (by omega) (by omega)).mpr this
--           have := this 2 (by norm_num)
--           norm_num at this; trivial
--       · constructor
--         · have : ¬ 2 ∣ a / 2 ^ a.factorization 2 := Nat.not_dvd_ordCompl (by norm_num) (by omega)
--           omega
--         · apply (Nat.ordProj_mul_ordCompl_eq_self a 2).symm




theorem GL2012AT2_2 {a : ℕ} (haA : ¬ a ∈ A) (ha : 2 ≤ a) :
            ∃ b : ℕ, 1 ≤ b ∧ b < 2 * a - 1 ∧ 2 * a ∣ b * (b + 1) := by
  by_cases isOdd : ¬ 2 ∣ a
  · use a
    constructor
    · linarith
    · constructor
      · omega
      · rw[mul_comm]
        apply mul_dvd_mul
        · simp
        · omega
  · simp at isOdd
    unfold A at haA; simp at haA
    have resa : ∃ t r : ℕ, 1 < r ∧ r % 2 = 1 ∧ a = 2 ^ t * r := by
      use Nat.factorization a 2, a / (2 ^ (Nat.factorization a 2))
      constructor
      · apply lt_iff_le_and_ne.mpr
        constructor
        · apply (Nat.one_le_div_iff (by positivity)).mpr
          apply Nat.ordProj_le
          linarith
        · by_contra! e
          have e : 2 ^ a.factorization 2 = a := by
            apply Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd _ _) e.symm
          apply haA (a.factorization 2 -1)
          rw[Nat.sub_add_cancel]; exact e.symm
          have : 2 ∣ a := by omega
          have := (Nat.factorization_prime_le_iff_dvd (by omega) (by omega)).mpr this
          have := this 2 (by norm_num)
          norm_num at this; trivial
      · constructor
        · have : ¬ 2 ∣ a / 2 ^ a.factorization 2 := Nat.not_dvd_ordCompl (by norm_num) (by omega)
          omega
        · apply (Nat.ordProj_mul_ordCompl_eq_self a 2).symm
    rcases resa with ⟨k,  m, h1, h2, h3⟩
    have res2a : 2 * a = 2 ^ (k + 1) * m := by rw[h3]; ring_nf
    have isCop : m.Coprime (2 ^ (k + 1)) := by
      apply Nat.Coprime.symm
      apply Nat.Coprime.pow_left
      apply (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by omega)
    have := Nat.chineseRemainder isCop (m - 1) 0
    set cr := Nat.chineseRemainder isCop (m - 1) 0 with cr_def
    have hx1 := cr.2.1
    have hx2 := cr.2.2
    use cr
    have : (cr : ℕ) ≠ 0 := by
        intro h
        rw[h] at hx1
        have := Nat.ModEq.add_le_of_lt hx1 (by omega)
        omega
    constructor
    · omega
    · constructor
      · rw[res2a]
        apply lt_iff_le_and_ne.mpr; constructor
        · have := Nat.chineseRemainder_lt_mul isCop (m-1) 0 (by omega) (by positivity)
          rw[←cr_def, mul_comm] at this
          apply (Nat.lt_iff_le_pred (by linarith)).mp this
        · intro h
          rw[h] at hx2
          have := Nat.ModEq.dvd hx2.symm
          norm_num at this; norm_cast at this
          have : 2 ^ (k + 1) ∣ 1 := by apply( Nat.dvd_sub_iff_right (by omega) (Nat.dvd_mul_right _ _)).mp this
          have : 2 ^ (k + 1) = 1 := Nat.dvd_one.mp this
          omega
      · rw[res2a]
        apply mul_dvd_mul
        · apply Nat.modEq_zero_iff_dvd.mp hx2
        · have h : ↑cr + 1 ≡ (m - 1) + 1 [MOD m] := Nat.ModEq.add_right 1 hx1
          have e1 : (m - 1) + 1 = m := by omega
          rw[e1] at h
          have : ↑cr + 1 ≡ 0 [MOD m] := by
            apply Nat.ModEq.trans h
            simp [Nat.modEq_iff_dvd]
          exact Nat.modEq_zero_iff_dvd.mp this



end section
