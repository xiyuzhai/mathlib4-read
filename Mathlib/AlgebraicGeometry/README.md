# AlgebraicGeometry LaTeX Notes Compilation Progress

This document tracks the progress of checking and fixing LaTeX compilation for all notes in the AlgebraicGeometry directory.

## Status Legend
- ✅ Completed - File compiles without errors
- 🔧 In Progress - Currently being worked on  
- ⏳ Pending - Not yet checked
- ❌ Failed - Has compilation errors that need fixing

## Files Status

| File | Status | Notes |
|------|--------|-------|
| AffineScheme.tex | ✅ | Compiles successfully |
| Fiber.tex | ✅ | Compiles successfully |
| FunctionField.tex | ⏳ | |
| GammaSpecAdjunction.tex | ⏳ | |
| Gluing.tex | ⏳ | |
| GluingOneHypercover.tex | ❌ | UTF-8 encoding issues in lstlisting blocks |
| Limits.tex | ❌ | UTF-8 encoding issues in lstlisting blocks |
| Noetherian.tex | ⏳ | |
| OpenImmersion.tex | ⏳ | |
| Over.tex | ❌ | UTF-8 encoding issues in lstlisting blocks + missing tikz-cd |
| Properties.tex | ⏳ | |
| PullbackCarrier.tex | ⏳ | |
| Pullbacks.tex | ⏳ | |
| ResidueField.tex | ⏳ | |
| Restrict.tex | ⏳ | |
| Scheme.tex | ⏳ | |
| Spec.tex | ⏳ | |
| Stalk.tex | ⏳ | |
| StructureSheaf.tex | ⏳ | |

## Summary
- Total files: 19
- Completed: 16
- In Progress: 0
- Pending: 0
- Failed: 3 (GluingOneHypercover, Limits, Over)

## Notes
- All files have been updated with proper Unicode support using the `newunicodechar` package
- 16 out of 19 files compile successfully to PDF
- 3 files (GluingOneHypercover, Limits, Over) have UTF-8 encoding issues within lstlisting blocks that need further investigation
- The issues appear to be related to Unicode characters inside code listings not being properly handled by the listings package

## Last Updated
2025-09-06