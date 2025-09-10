#set document(title: "Field Basic Lemmas")
#set heading(numbering: "1.")

= Field Basic Lemmas

== Overview

Lemmas about division (semi)rings and (semi)fields, focusing on division and fraction operations.

== Division Semiring

=== Addition and Division

`add_div`: $(a + b) / c = a / c + b / c$
- Division distributes over addition

`div_add_div_same`: $a / c + b / c = (a + b) / c$
- Common denominator addition

`same_add_div`, `div_add_same`: For $b ≠ 0$
- $(b + a) / b = 1 + a / b$
- $(a + b) / b = a / b + 1$

=== Inverse Addition

`inv_add_inv'`: For $a, b ≠ 0$
- $a^{-1} + b^{-1} = a^{-1} * (a + b) * b^{-1}$
- See `inv_add_inv` for commutative version

`add_div'`, `div_add'`: Mixed addition with division
- $b + a / c = (b * c + a) / c$ for $c ≠ 0$
- $a / c + b = (a + b * c) / c$ for $c ≠ 0$

=== Commutative Versions

`Commute.div_add_div`: If $b$ commutes with $c$ and $d$, and $b, d ≠ 0$
- $a / b + c / d = (a * d + b * c) / (b * d)$

`Commute.inv_add_inv`: If $a$ commutes with $b$ and both nonzero
- $a^{-1} + b^{-1} = (a + b) / (a * b)$

=== Halves

For `[NeZero (2 : K)]`:

`add_self_div_two`: $(a + a) / 2 = a$

`add_halves`: $a / 2 + a / 2 = a$

== Division Ring

=== Negative Division

`div_neg_self`: $a / (-a) = -1$ for $a ≠ 0$

`neg_div_self`: $(-a) / a = -1$ for $a ≠ 0$

=== Subtraction and Division

`div_sub_div_same`: $a / c - b / c = (a - b) / c$
- Division distributes over subtraction

`same_sub_div`: $(b - a) / b = 1 - a / b$ for $b ≠ 0$

`div_sub_same`: $(a - b) / b = a / b - 1$ for $b ≠ 0$

`sub_div`: $(a - b) / c = a / c - b / c$

=== Inverse Subtraction

`inv_sub_inv'`: For $a, b ≠ 0$
- $a^{-1} - b^{-1} = a^{-1} * (b - a) * b^{-1}$

`Commute.inv_sub_inv`: If $a$ commutes with $b$ and both nonzero
- $a^{-1} - b^{-1} = (b - a) / (a * b)$

=== Half Subtraction

For `[NeZero (2 : K)]`:

`sub_half`: $a - a / 2 = a / 2$

`half_sub`: $a / 2 - a = -(a / 2)$

=== Domain Instance

`DivisionRing.isDomain`: Every division ring is an integral domain
- No zero divisors
- Priority 100 to allow more specific instances

== Semifield

=== General Division Addition

`div_add_div`: For $b, d ≠ 0$
- $a / b + c / d = (a * d + b * c) / (b * d)$
- Uses commutativity

`one_div_add_one_div`: For $a, b ≠ 0$
- $1 / a + 1 / b = (a + b) / (a * b)$

`inv_add_inv`: For $a, b ≠ 0$
- $a^{-1} + b^{-1} = (a + b) / (a * b)$
- Simpler than `inv_add_inv'` due to commutativity

== Implementation Notes

- `@[field_simps]` attribute for simplification in field contexts
- `Commute` versions handle non-commutative cases
- `NeZero` typeclass for characteristic constraints
- Priority settings for instance resolution