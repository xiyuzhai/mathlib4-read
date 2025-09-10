#set document(title: "Ideal Sheaf (Deprecated)")
#set heading(numbering: "1.")

= Ideal Sheaf (Deprecated)

== Overview

This module has been deprecated since 2025-04-13.

== Deprecation Notice

The functionality previously in `IdealSheaf.lean` has been moved to:
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`

Users should import the new module directly.

== Migration

Replace imports of:
```lean
import Mathlib.AlgebraicGeometry.IdealSheaf
```

With:
```lean
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
```