#set document(title: "Gradients in Hilbert Spaces")
#set heading(numbering: "1.")
#set page(margin: 2cm)

= Gradients in Hilbert Spaces

== Overview

This module defines gradients for functions from Hilbert spaces to scalars ($ℝ$ or $ℂ$), establishing the connection between gradients and Fréchet derivatives. The gradient provides a concrete vector representation of the derivative in inner product spaces.

== Core Definitions

=== HasGradientAtFilter
A function $f : F → 𝕜$ has gradient $f'$ at $x$ along filter $L$ if:
$$f(x') = f(x) + angle.l f', x' - x angle.r + o(‖x' - x‖)$$
as $x' → x$ along the filter $L$.

This is equivalent to having Fréchet derivative $"toDual"(f')$ at $x$ along $L$.

=== HasGradientWithinAt
The gradient exists within a set $s$ if the above holds for $x'$ converging to $x$ inside $s$:
$$"HasGradientWithinAt" space f space f' space s space x ⟺ "HasGradientAtFilter" space f space f' space x space (cal(N)[s] x)$$

=== HasGradientAt
The gradient exists at a point if:
$$"HasGradientAt" space f space f' space x ⟺ "HasGradientAtFilter" space f space f' space x space (cal(N) x)$$

This is the unrestricted version where $x'$ can approach from any direction.

== The Gradient Function

=== Definition
The gradient of $f$ at $x$ is defined as:
$$nabla f(x) = ("toDual" space 𝕜 space F)^(-1) ("fderiv" space 𝕜 space f space x)$$

If the derivative doesn't exist, the gradient is defined to be zero.

=== Notation
Within the `Gradient` namespace, $nabla$ denotes the gradient operator.

=== Gradient Within Sets
For restricted domains:
$$"gradientWithin" space f space s space x = ("toDual" space 𝕜 space F)^(-1) ("fderivWithin" space 𝕜 space f space s space x)$$

== Relationship with Fréchet Derivatives

=== Equivalence Theorems

The gradient and Fréchet derivative are related by the Riesz representation theorem:

1. **HasGradient ↔ HasFDeriv**:
   - $"HasGradientAt" space f space f' space x ⟺ "HasFDerivAt" space f space ("toDual" space f') space x$
   - The dual map sends the gradient vector to the corresponding linear functional

2. **Conversion Functions**:
   - If $f$ has Fréchet derivative $L$, then gradient is $("toDual")^(-1)(L)$
   - If $f$ has gradient $g$, then Fréchet derivative is $"toDual"(g)$

== Uniqueness and Existence

=== Uniqueness
If $f$ has gradients $g_1$ and $g_2$ at $x$, then $g_1 = g_2$.

This follows from uniqueness of Fréchet derivatives and injectivity of the dual map.

=== Existence Conditions
- **DifferentiableAt** $⟹$ **HasGradientAt**: If $f$ is differentiable at $x$, then $nabla f(x)$ exists
- **HasGradientAt** $⟹$ **DifferentiableAt**: If gradient exists, function is differentiable

The gradient exists if and only if the function is Fréchet differentiable.

== One-Dimensional Case

=== Complex Scalars
When $F = 𝕜$ (one-dimensional), the gradient relates to the ordinary derivative:
$$nabla g(u) = overline("deriv" space g(u))$$

The conjugate appears because the gradient uses the inner product structure.

=== Real Scalars
For $g : ℝ → ℝ$:
$$nabla g(u) = "deriv" space g(u)$$

No conjugation needed since $ℝ$ has trivial conjugation.

== Key Properties

=== Congruence
The gradient respects function equality:
- If $f = g$ on a neighborhood of $x$, then $nabla f(x) = nabla g(x)$
- Gradient is a local property

=== Constant Functions
For constant $f$:
$$nabla f = 0$$

=== Continuity
If $f$ has a gradient at $x$, then $f$ is continuous at $x$.

More generally:
- **HasGradientWithinAt** $⟹$ **ContinuousWithinAt**
- **HasGradientAt** $⟹$ **ContinuousAt**

== Computational Rules

=== Linearity
The gradient is linear in the function:
$$nabla(alpha f + beta g) = alpha space nabla f + beta space nabla g$$
(when both gradients exist)

=== Chain Rule
For composed functions (developed in other modules):
$$nabla(g compose f)(x) = (f'(x))^t nabla g(f(x))$$
where $(f'(x))^t$ is the adjoint (transpose) of the derivative.

=== Product Rule
For products of scalar functions (in extended modules):
$$nabla(f g) = g space nabla f + f space nabla g$$

== Applications

=== Optimization
- Critical points: $nabla f(x) = 0$ for local extrema
- Gradient descent: $x_{n+1} = x_n - alpha nabla f(x_n)$
- Steepest descent direction: $-nabla f(x) / ‖nabla f(x)‖$

=== PDEs
- Heat equation: $partial_t u = Delta u = "div"(nabla u)$
- Laplace equation: $Delta u = 0$
- Gradient flows in infinite dimensions

=== Variational Calculus
- Euler-Lagrange equations via gradients
- Energy minimization problems
- Shape optimization

== Design Notes

The module uses the Riesz representation theorem implicitly through the `toDual` isomorphism. This provides a clean separation between the geometric notion of gradient (a vector) and the analytic notion of derivative (a linear functional).

The choice to define gradient as zero when the derivative doesn't exist simplifies many statements and aligns with common practice in optimization.