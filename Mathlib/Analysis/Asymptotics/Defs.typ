#set document(title: "Asymptotic Analysis - Big O and Little o")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Asymptotic Analysis - Big O and Little o

== Overview

This module formalizes asymptotic comparisons between functions using Big O, Little o, and related notations. These tools are fundamental for analyzing algorithm complexity, approximation quality, and limiting behavior in analysis. The framework works for functions between arbitrary normed spaces, not just real-valued functions.

== Core Relations

=== IsBigOWith
The foundational relation `IsBigOWith c l f g` means that eventually along filter `l`:
$$‖f(x)‖ ≤ c dot ‖g(x)‖$$

This captures the idea that $f$ is bounded by a constant multiple of $g$ near the limit point of filter `l`.

Key properties:
- The constant $c$ is explicit
- Works for any filter (at infinity, at a point, etc.)
- Domain and codomain can be different types

=== Big O Notation
The relation `f =O[l] g` means there exists some constant $c$ such that:
$$∃ c in ℝ, ∀^F x in l, ‖f(x)‖ ≤ c dot ‖g(x)‖$$

Equivalent formulations:
- $∃ c > 0$, eventually $‖f(x)‖ ≤ c dot ‖g(x)‖$
- $∃ c > 0$, eventually $c dot ‖f(x)‖ ≤ ‖g(x)‖$
- The ratio $‖f(x)‖ / ‖g(x)‖$ is eventually bounded

=== Little o Notation
The relation `f =o[l] g` means that for every positive constant:
$$∀ c > 0, ∀^F x in l, ‖f(x)‖ ≤ c dot ‖g(x)‖$$

This captures that $f$ becomes negligible compared to $g$:
- The ratio $‖f(x)‖ / ‖g(x)‖ → 0$ along `l`
- $f$ is dominated by arbitrarily small multiples of $g$

== Relationships Between Notations

=== Hierarchy
The relations form a strict hierarchy:
1. `f =o[l] g` implies `f =O[l] g`
2. `f =o[l] g` implies `IsBigOWith c l f g` for any $c > 0$
3. `IsBigOWith c l f g` implies `f =O[l] g`

=== Conversions
- **Little o to Big O**: Every little o relation is also big O
- **Big O to IsBigOWith**: If $f = O(g)$, then $∃ c$, `IsBigOWith c l f g`
- **IsBigOWith to Big O**: Any `IsBigOWith` relation gives big O

== Filter Flexibility

The framework works with any filter `l`:

=== Common Filters
- **At infinity**: `l = atTop` for $x → ∞$
- **At a point**: `l = 𝓝 a` for $x → a$
- **Within a set**: `l = 𝓝[s] a` for approach within $s$
- **Along a sequence**: `l = atTop.map u` for sequences

=== Examples
- $sin(x) = O["atTop"](1)$ - sine is bounded
- $x^2 = o[cal(N) space 0](x)$ - quadratic vanishes faster than linear near 0
- $e^x = o["atTop"](e^(2x))$ - exponential growth rates

== Special Cases

=== Functions to Normed Fields
When $g : α → 𝕜$ where $𝕜$ is a normed field and $g(x) ≠ 0$:
$$f = o[l](g) ⟺ "Tendsto"(x ↦ f(x)/g(x), l, 𝓝(0))$$

This connects little o to the familiar notion of limit.

=== Real-Valued Functions
For $f, g : α → ℝ$:
- The norm is just absolute value
- $f = O(g)$ means $|f| ≤ c|g|$ eventually
- Captures growth rates in analysis of algorithms

=== Vector-Valued Functions
The framework handles vector spaces naturally:
- Compare magnitudes via norms
- No need to work component-wise
- Preserves geometric intuition

== Algebraic Properties

=== Transitivity
- If $f = O(g)$ and $g = O(h)$, then $f = O(h)$
- If $f = o(g)$ and $g = o(h)$, then $f = o(h)$
- If $f = o(g)$ and $g = O(h)$, then $f = o(h)$

=== Arithmetic Operations
The relations interact well with arithmetic:
- $O(f) + O(f) = O(f)$
- $o(f) + o(f) = o(f)$
- $O(f) dot O(g) = O(f dot g)$
- Constants: $c dot O(f) = O(f)$ for $c ≠ 0$

=== Composition
For continuous functions:
- If $f = O(g)$ and $h$ continuous, then $h compose f = O(h compose g)$ (under conditions)

== Applications

=== Algorithm Analysis
- Time complexity: $T(n) = O(n log n)$
- Space complexity: $S(n) = o(n^2)$
- Average vs worst case analysis

=== Numerical Analysis
- Truncation error: $e_n = O(h^p)$ for $p$-th order methods
- Convergence rates: $‖x_n - x^*‖ = o(r^n)$
- Condition numbers and stability

=== Asymptotic Expansions
- Taylor series: $f(x) = ∑_{k=0}^n a_k x^k + o(x^n)$
- Stirling's formula: $n! ∼ sqrt(2 pi n)(n/e)^n$
- Stationary phase approximations

=== Probability Theory
- Law of large numbers: $S_n/n - μ = o(1)$ a.s.
- Central limit theorem rates
- Large deviation principles

== Design Philosophy

=== Generality
The module is designed for maximum generality:
- Arbitrary normed spaces (not just reals)
- Any filter (not just limits at infinity)
- Separate types for domain and codomain

=== Irreducibility
Core definitions are marked `irreducible`:
- Prevents unwanted unfolding
- Explicit lemmas for working with definitions
- Better proof performance

=== Notation
Standard mathematical notation:
- `f =O[l] g` for big O
- `f =o[l] g` for little o
- Filter annotation `[l]` makes limit point explicit

== Related Concepts

The module connects to:
- **Theta notation** (tight bounds): $f = Θ(g)$ means $f = O(g)$ and $g = O(f)$
- **Asymptotic equivalence**: $f ∼ g$ means $f/g → 1$
- **Growth rates**: Logarithmic, polynomial, exponential hierarchies
- **Regularity theory**: Hölder and Lipschitz continuity as special cases