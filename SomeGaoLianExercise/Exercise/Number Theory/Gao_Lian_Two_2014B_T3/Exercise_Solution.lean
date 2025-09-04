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




theorem GL2014BT3 (hanz : a ≠ 0) (_ : b ≠ 0) (abOdd : (a + b)%2 = 1) (hk : 2 ≤ k)
          (P : ∃ x y :  ℤ, a ^ k * x - b ^ k *  y = a - b ∧ 0 < |x - y| ∧ |x - y| ≤ 2):
              ∃ n : ℤ , |a - b| = n ^ k := by
    set d := ((Int.gcd a b) : ℤ) with d_def
    have d_dvd_a : d ∣ a := Int.gcd_dvd_left  a b
    have d_dvd_b : d ∣ b := Int.gcd_dvd_right a b
    rcases d_dvd_a with ⟨a₁, haa_1⟩
    rcases d_dvd_b with ⟨b₁, hbb_1⟩
    have d_pos : 0 < d := by rw[d_def]; norm_num; left; exact hanz

    have ab_1_co : (a₁).gcd b₁ = 1 := by
        rw[haa_1, hbb_1] at d_def
        rw[Int.gcd_mul_left, Nat.cast_mul, Nat.cast_natAbs] at d_def
        have : |d| = d := by apply abs_eq_self.mpr; rw[d_def]; apply mul_nonneg; simp; norm_cast; apply Nat.zero_le
        rw[this] at d_def; norm_num at d_def;
        have := by refine Int.eq_one_of_mul_eq_self_right ?_ d_def.symm; apply ne_of_gt; assumption
        norm_num at this; trivial

    rcases P with ⟨x, y, P1, P2, P3⟩

    have ev : d ^(k - 1) * (a₁ ^ k * x - b₁ ^ k * y) = a₁ - b₁ := by
        rw[haa_1, hbb_1] at P1; ring_nf at P1; ring_nf
        have : d * (d ^ (k - 1) * a₁ ^ k * x - d ^ (k - 1) * b₁ ^ k * y) = d * (a₁ - b₁) := by
            ring_nf; nth_rw 1 3 [←pow_one d, ←pow_add, ←pow_add]
            have : 1 + (k - 1) = k := by omega
            rwa[this]
        field_simp at this; rcases this with this | this
        · trivial
        · linarith

    have dk_dvd_ab_1 : d ^(k - 1) ∣ a₁ - b₁ := by
        use (a₁ ^ k * x - b₁ ^ k * y)
        exact ev.symm

    have transf_ev : d ^(k - 1) * a₁ ^ k * (x - y) + d ^ (k - 1) * (a₁ ^ k - b₁ ^ k) * y = a₁ - b₁ := by
        linarith

    have dvd_pow_k : a₁ - b₁ ∣ a₁ ^ k - b₁ ^ k := by
        exact sub_dvd_pow_sub_pow a₁ b₁ k

    have ab_1_dvd_mul : a₁ - b₁ ∣ d ^ (k-1) * a₁ ^ k * (x - y) := by
        have : d ^ (k-1) * a₁ ^ k * (x - y) =  d ^ (k - 1) * a₁ ^ k * (x - y) + d ^ (k - 1) * (a₁ ^ k - b₁ ^ k) * y - d ^ (k - 1) * (a₁ ^ k - b₁ ^ k) * y :=
            by ring_nf
        rw[this]; apply dvd_sub
        · use 1; rw[mul_one]; trivial
        · apply dvd_mul_of_dvd_left
          apply dvd_mul_of_dvd_right
          trivial

    have ab_1_dvd_d : a₁ - b₁ ∣ d ^ (k - 1) := by
        rw [mul_assoc] at ab_1_dvd_mul
        apply Int.dvd_of_dvd_mul_left_of_gcd_one ab_1_dvd_mul
        have : (a₁ - b₁).gcd (a₁ ^ k) = 1 := by
            apply Int.gcd_pow_right_of_gcd_eq_one
            rw[Int.gcd_self_sub_left, Int.gcd_comm]
            trivial
        rw[Int.gcd_mul_right_right_of_gcd_eq_one this]
        have : x - y = -2 ∨ x - y = -1 ∨ x - y = 1 ∨ x - y = 2 := by
            have this1: -2 ≤ x - y ∧ x - y ≤ 2 := by
                apply abs_le.mp P3
            have this2 : x - y ≠ 0 := by apply abs_pos.mp P2
            have infbon : -2 ≤ x - y := this1.1
            have subbon : x - y ≤ 2 :=  this1.2
            interval_cases (x - y)
            all_goals norm_num
            contradiction
        have ab_1_co_2 : (a₁ - b₁).gcd 2 = 1 := by
            have h : (a - b) % 2 = 1 := by
                rw[←Int.add_sub_cancel a b, sub_sub, Int.sub_emod, abOdd, ←mul_two, Int.mul_emod_left]; norm_num
            have d_odd : d % 2 = 1 := by
                have : ¬ 2 ∣ d := by
                    intro h
                    rcases h with ⟨k, dk⟩
                    rw[haa_1, hbb_1, dk, ←mul_add, mul_assoc, Int.mul_emod_right] at abOdd
                    trivial
                norm_num at this; trivial
            rw[haa_1, hbb_1, ←mul_sub, Int.mul_emod, d_odd, one_mul] at h
            norm_num at h
            have : ∃ r, a₁ - b₁ = 2 * r + 1 := by
                use (a₁ - b₁) / 2
                have := by apply Int.ediv_add_emod (a₁ - b₁) 2
                rwa[h, eq_comm] at this
            rcases this with ⟨r, hr⟩
            rw[hr, Int.gcd_mul_left_add_left, Int.gcd_one_left]
        rcases this with h | h | h | h
        <;> rw[h];
        · simp; trivial
        · simp
        · apply Int.gcd_one_right (a₁ - b₁)
        · trivial

    have dk_dvd_ab_1' : d ^ (k - 1) ∣ (a₁ - b₁).natAbs  := Int.dvd_natAbs.mpr dk_dvd_ab_1
    have ab_1_dvd_d' : ((a₁ - b₁).natAbs : ℤ) ∣ d ^ (k - 1) := Int.natAbs_dvd.mpr ab_1_dvd_d
    have key : d ^ (k - 1) = (a₁ - b₁).natAbs := by
        apply le_antisymm
        · refine Int.le_of_dvd ?_ dk_dvd_ab_1'
          norm_num
          have h : (a - b) % 2 = 1 := by
                rw[←Int.add_sub_cancel a b, sub_sub, Int.sub_emod, abOdd, ←mul_two, Int.mul_emod_left]; norm_num
          intro h'; rw [haa_1, hbb_1, ←mul_sub, h', mul_zero] at h; norm_num at h
        · apply Int.le_of_dvd (by positivity) ab_1_dvd_d'
    norm_cast at key

    use d
    rw[haa_1, hbb_1, ←mul_sub, abs_mul, ←key]
    have : |d| = d := by apply abs_eq_self.mpr (by linarith)
    nth_rw 1 [this, ←pow_one d, ←pow_add]
    have : 1 + (k - 1) = k := by omega
    rw[this]






end section
