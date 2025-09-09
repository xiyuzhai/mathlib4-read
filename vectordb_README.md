# Mathlib Vector Database System

A comprehensive search infrastructure for Mathlib that combines readable documentation with semantic search capabilities.

## Features

- **Multi-modal Search**: Semantic search via embeddings + structured filtering
- **Type-aware Filtering**: Search only theorems, definitions, classes, etc.
- **Module Scoping**: Limit search to specific modules (e.g., Analysis, Algebra)
- **Typst Documentation**: Human-readable PDF documentation for each module
- **Local or Cloud Embeddings**: Use Sentence Transformers locally or OpenAI API

## Installation

```bash
pip install -r requirements.txt
```

## Usage

### Building the Vector Database

```bash
# Index all of Mathlib
python extract_mathlib_to_vectordb.py --mathlib-path Mathlib

# Test with limited files
python extract_mathlib_to_vectordb.py --mathlib-path Mathlib --limit 100
```

### Searching

```bash
# Basic semantic search
python extract_mathlib_to_vectordb.py --search "Cauchy-Schwarz inequality"

# Filter by type
python extract_mathlib_to_vectordb.py --search "convex sets" --filter-type theorem

# Filter by module
python extract_mathlib_to_vectordb.py --search "norm properties" --filter-module Mathlib.Analysis.Normed
```

## Database Schema

Each indexed item contains:
- **name**: Symbol name
- **type**: def, theorem, lemma, class, structure, instance, inductive
- **content**: First few lines of the definition
- **docstring**: Associated documentation if present
- **file_path**: Source file location
- **line_number**: Line number in source
- **module_path**: Full module path (e.g., Mathlib.Analysis.Convex.Basic)
- **dependencies**: Import statements

## Typst Documentation

For each Lean file, create accompanying Typst documentation:

```bash
# Compile individual documentation
typst compile Mathlib/Analysis/Normed/Group/Basic.typ

# View PDF
open Mathlib/Analysis/Normed/Group/Basic.pdf
```

## Architecture

```
mathlib4-read/
├── Mathlib/                      # Lean source files
│   └── Analysis/
│       ├── Normed/
│       │   └── Group/
│       │       ├── Basic.lean    # Original Lean file
│       │       ├── Basic.typ     # Typst documentation
│       │       └── Basic.pdf     # Compiled PDF
│       └── ...
├── extract_mathlib_to_vectordb.py # Main extraction script
├── mathlib_vectordb/              # ChromaDB storage
└── requirements.txt               # Python dependencies
```

## Query Examples

### Find all convexity theorems
```python
results = db.search(
    "properties of convex sets",
    filter_type="theorem",
    filter_module="Mathlib.Analysis.Convex"
)
```

### Find norm-related definitions
```python
results = db.search(
    "norm and metric properties",
    filter_type="def",
    n_results=20
)
```

### Natural language queries
```python
results = db.search(
    "How do I prove that the intersection of convex sets is convex?"
)
```

## Future Enhancements

- [ ] Graph database for dependency analysis
- [ ] API server for web-based search
- [ ] Integration with Lean LSP
- [ ] Automatic Typst generation for all files
- [ ] Cross-reference linking in documentation
- [ ] Proof complexity metrics
- [ ] Usage examples extraction