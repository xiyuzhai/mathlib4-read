#set text(font: "New Computer Modern", size: 11pt)
#set page(margin: 1in)
#set heading(numbering: "1.")

= Module Overview

== \1

This file gathers basic facts of analytic nature on the complex numbers.

== \1

This file registers `\1* as a normed field, expresses basic properties of the norm, and gives tools
on the real vector space structure of `\1*. Notably, it defines the following functions in the
namespace `\1*.

|Name              |Type         |Description                                             |
|------------------|-------------|--------------------------------------------------------|
|`\1*|\mathbb{C} ≃L[\mathbb{R}] \mathbb{R} \times \mathbb{R}|The natural `\1} from `\1} to `\1} |
|`\1*           |\mathbb{C} \toL[\mathbb{R}] \mathbb{R}    |Real part function as a `\1}           |
|`\1*           |\mathbb{C} \toL[\mathbb{R}] \mathbb{R}    |Imaginary part function as a `\1}      |
|`\1*       |\mathbb{R} \toL[\mathbb{R}] \mathbb{C}    |Embedding of the reals as a `\1}       |
|`\1*        |\mathbb{R} \toₗᵢ[\mathbb{R}] \mathbb{C}   |Embedding of the reals as a `\1}            |
|`\1*         |\mathbb{C} ≃L[\mathbb{R}] \mathbb{C}    |Complex conjugation as a `\1}        |
|`\1*         |\mathbb{C} ≃ₗᵢ[\mathbb{R}] \mathbb{C}   |Complex conjugation as a `\1}          |

We also register the fact that `\1* is an `\1} field.

= Key Definitions

A theorem defining `continuous_normSq*

A theorem defining `nnnorm_eq_one_of_pow_eq_one*

A theorem defining `norm_eq_one_of_pow_eq_one*

A lemma defining `le_of_eq_sum_of_eq_sum_norm*

A theorem defining `equivRealProd_apply_le*

A theorem defining `equivRealProd_apply_le*

A theorem defining `lipschitz_equivRealProd*

A theorem defining `antilipschitz_equivRealProd*

A theorem defining `isUniformEmbedding_equivRealProd*

A def defining `equivRealProdCLM*

= Main Theorems

The `normSq` function on `\mathbb{C*` is proper.

The only continuous ring homomorphism from `\mathbb{R*` to `\mathbb{C}` is the identity.

The slit plane includes the open unit ball of radius `1` around `1`.

The slit plane includes the open unit ball of radius `1` around `1`.
