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