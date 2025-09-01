import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.ModEq

import SomeGaoLIanExercise



/-
---------------------------------------------------------------------------------------
    # 2013 年高中联赛 $\cdot$ 二试 (B卷)

    ## 第一题

    设 $n$ 是正整数, 求证 : 不存在三个奇数 $x, y, z$, 满足

    $$(x + y) ^ n + (y + z) ^ n = (z + x) ^ n.$$

    ---

    ## 答案

    假设存在

    由 $x, y, z$ 是整数可知, $x + y, y + z, z + x$ 都是偶数, 在方程两边同时除以 $2 ^ n$ 得,

    $$(\frac{x+y}{2})^n + (\frac{y+z}{2})^n = (\frac{z+x}{2})^n.$$

    因为对整数 $a$, $a^n \equiv a \:(\mathrm{mod}\;2)$ , 所以

    $$\frac{x+y}{2} + \frac{y+z}{2}  \equiv \frac{z+x}{2}\quad(\mathrm{mod}\;2) $$

    即 $y \equiv 0 \; (\mathrm{mod}\; 2)$. 这与 $y$ 是奇数矛盾 !

    从而命题得证. $\square$
---------------------------------------------------------------------------------------
-/


section

variable (n : ℕ) (hn : 1 ≤ n) (x y z : ℤ) (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1)

example : (x + y) ^ n + (y + z) ^ n ≠ (x + z) ^ n :=
  sorry


#check Int.ModEq.pow_card_sub_one_eq_one


lemma pow_eq_self_mod_two (n : ℕ) (hn : 1 ≤ n) (a : ℤ) : a ^ n ≡ a [ZMOD 2] := by
  by_cases h : a % 2 = 1
  · have := Int.mod_modEq a 2
    rw[h] at this
    have this2 :=Int.ModEq.pow n this
    rw[one_pow] at this2
    apply Int.ModEq.trans this2.symm this
  · simp at h
    have := Int.modEq_zero_iff_dvd.mpr h
    apply Int.ModEq.trans _ this.symm
    have := Int.ModEq.pow n this
    rwa[zero_pow (by linarith)] at this

lemma Int_id_change (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1) (h : (x + y) ^ n + (y + z) ^ n = (z + x) ^ n) :
        ((x + y) / 2) ^ n + ((y + z) / 2) ^ n = ((z + x) / 2) ^ n := by
  set a := (x : ℝ)
  set b := (y : ℝ)
  set c := (z : ℝ)
  have evenxy : 2 ∣ x + y := by omega
  have evenyz : 2 ∣ y + z := by omega
  have evenzx : 2 ∣ z + x := by omega
  have h_real : (a + b) ^ n + (b + c) ^ n = (c + a) ^ n := by
      unfold a b c
      norm_cast
  have result_real : ((a + b) / 2) ^ n +( (b + c) / 2) ^ n = ((c + a) / 2) ^ n := by
    field_simp; trivial
  unfold a b c at result_real
  rw[←Int.cast_add, ←Int.cast_add, ←Int.cast_add, ←Int.cast_two, ←Int.cast_div evenxy, ←Int.cast_div evenyz, ←Int.cast_div evenzx, ←Int.cast_pow, ←Int.cast_pow, ←Int.cast_pow, ←Int.cast_add] at result_real
  norm_cast at result_real
  repeat norm_num

theorem GL2013BT1 (hn : 1 ≤ n) (hx : x % 2 = 1) (hy : y % 2 = 1) (hz : z % 2 = 1) : (x + y) ^ n + (y + z) ^ n ≠ (z + x) ^ n := by
  intro h
  have evenxy : 2 ∣ x + y := by omega
  have evenyz : 2 ∣ y + z := by omega
  have evenzx : 2 ∣ z + x := by omega
  have : (x + y) / 2 + (y + z) / 2 ≡ (z + x) / 2 [ZMOD 2] := by
    have m1 : ((x + y) / 2) ^ n + ((y + z) / 2) ^ n ≡ (x + y) / 2 + (y + z) / 2 [ZMOD 2] := by
      have t1 := pow_eq_self_mod_two n hn ((x + y) / 2)
      have t2 := pow_eq_self_mod_two n hn ((y + z) / 2)
      apply Int.ModEq.add t1 t2
    have m2 := pow_eq_self_mod_two n hn ((z + x) / 2)
    have e1 := Int_id_change n _ _ _ hx hy hz h
    rw[←e1] at m2
    apply Int.ModEq.trans m1.symm m2
  rw[Int.ModEq] at this
  omega













end section
