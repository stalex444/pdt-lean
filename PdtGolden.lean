import Mathlib

namespace PDT

/-- (a) Discriminant of the depressed cubic `t³ + p t + q` is `−4p³ − 27q²`.
For `x³ − x − 1` we have `p = −1, q = −1`, giving `−4(−1)³ − 27(−1)² = −23`. -/
theorem disc_cubic : (-4*(-1:ℤ)^3 - 27*(-1)^2) = -23 := by decide

/-- (b) `dim su(3) + dim su(4) = (3²−1) + (4²−1) = 23`. -/
theorem dim_su3_su4 : ((3^2 - 1) + (4^2 - 1) : ℤ) = 23 := by decide

/-- (c) The "23" weld: `−disc(x³−x−1) = dim su(3) + dim su(4)`, both `= 23`. -/
theorem twentythree_weld :
    -(-4*(-1:ℤ)^3 - 27*(-1)^2) = (3^2 - 1) + (4^2 - 1) := by decide

/-- (d) `N(Q) = −1`: for `x⁴ − x − 1` the constant term is `−1`, and the product
of the four roots (the norm) is `(−1)⁴ · (const) = −1`. So `Q` is a unit of norm `−1`. -/
theorem unit_norm_Q : ((-1:ℤ))^4 * (-1) = -1 := by decide

/-- `N(ρ) = 1`: for `x³ − x − 1` the constant term is `−1`, and the product of the
three roots (the norm) is `(−1)³ · (const) = 1`. So `ρ` is a unit of norm `1`. -/
theorem unit_norm_rho : ((-1:ℤ))^3 * (-1) = 1 := by decide

end PDT
