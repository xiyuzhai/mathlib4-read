#!/usr/bin/env python3
"""
Extract Mathlib content to a vector database for semantic search.

This script:
1. Parses all .lean files in Mathlib
2. Extracts definitions, theorems, lemmas, classes, structures
3. Generates embeddings using OpenAI or local models
4. Stores in ChromaDB with metadata for filtering
"""

import os
import re
import json
from pathlib import Path
from typing import List, Dict, Any, Optional
from dataclasses import dataclass, asdict
import hashlib

# Vector DB and embedding imports
try:
    import chromadb
    from chromadb.config import Settings
except ImportError:
    print("Please install chromadb: pip install chromadb")
    exit(1)

try:
    from sentence_transformers import SentenceTransformer
    USE_LOCAL_EMBEDDINGS = True
except ImportError:
    USE_LOCAL_EMBEDDINGS = False
    print("Warning: sentence-transformers not found. Install for local embeddings.")

@dataclass
class LeanDefinition:
    """Represents a Lean definition/theorem/lemma."""
    name: str
    type: str  # 'def', 'theorem', 'lemma', 'class', 'structure', 'instance', 'inductive'
    content: str
    docstring: Optional[str]
    file_path: str
    line_number: int
    module_path: str  # e.g., "Mathlib.Analysis.Normed.Group.Basic"
    dependencies: List[str]  # imports
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
    
    def get_id(self) -> str:
        """Generate unique ID for this definition."""
        content = f"{self.file_path}:{self.name}:{self.line_number}"
        return hashlib.md5(content.encode()).hexdigest()

class LeanParser:
    """Parse Lean files to extract definitions and documentation."""
    
    # Patterns for different Lean constructs
    PATTERNS = {
        'def': re.compile(r'^(def|abbrev)\s+(\w+)', re.MULTILINE),
        'theorem': re.compile(r'^(theorem|lemma)\s+(\w+)', re.MULTILINE),
        'class': re.compile(r'^(class|structure)\s+(\w+)', re.MULTILINE),
        'inductive': re.compile(r'^(inductive)\s+(\w+)', re.MULTILINE),
        'instance': re.compile(r'^(instance)\s+(?:(\w+)\s*:)?\s*(.+?)(?:\s+where|\s*:=)', re.MULTILINE),
        'docstring': re.compile(r'/--(.+?)--/', re.DOTALL),
        'import': re.compile(r'^import\s+(.+)$', re.MULTILINE),
    }
    
    def parse_file(self, file_path: Path) -> List[LeanDefinition]:
        """Parse a single Lean file."""
        definitions = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            return definitions
        
        # Extract imports
        imports = self.PATTERNS['import'].findall(content)
        
        # Extract module path from file path
        module_path = str(file_path.with_suffix('')).replace('/', '.')
        
        # Extract docstrings
        docstrings = {}
        for match in self.PATTERNS['docstring'].finditer(content):
            # Simple heuristic: associate docstring with next definition
            docstring_end = match.end()
            docstring_text = match.group(1).strip()
            # Find next line number
            line_num = content[:docstring_end].count('\n') + 1
            docstrings[line_num] = docstring_text
        
        # Extract definitions
        for pattern_name, pattern in self.PATTERNS.items():
            if pattern_name in ['docstring', 'import']:
                continue
                
            for match in pattern.finditer(content):
                line_num = content[:match.start()].count('\n') + 1
                
                if pattern_name == 'instance':
                    # Instance might not have a name
                    def_type = match.group(1)
                    def_name = match.group(2) or f"instance_line_{line_num}"
                else:
                    def_type = match.group(1)
                    def_name = match.group(2)
                
                # Get the full definition (simplified - just first 5 lines)
                start_pos = match.start()
                lines = content[start_pos:].split('\n')[:5]
                def_content = '\n'.join(lines)
                
                # Check for associated docstring
                docstring = None
                for doc_line in range(max(1, line_num - 5), line_num):
                    if doc_line in docstrings:
                        docstring = docstrings[doc_line]
                        break
                
                definitions.append(LeanDefinition(
                    name=def_name,
                    type=def_type,
                    content=def_content,
                    docstring=docstring,
                    file_path=str(file_path),
                    line_number=line_num,
                    module_path=module_path,
                    dependencies=imports
                ))
        
        return definitions

class MathLibVectorDB:
    """Manage vector database for Mathlib content."""
    
    def __init__(self, db_path: str = "./mathlib_vectordb", use_local_embeddings: bool = True):
        """Initialize the vector database."""
        self.db_path = db_path
        
        # Initialize ChromaDB
        self.client = chromadb.PersistentClient(
            path=db_path,
            settings=Settings(anonymized_telemetry=False)
        )
        
        # Create or get collection
        self.collection = self.client.get_or_create_collection(
            name="mathlib_definitions",
            metadata={"description": "Mathlib definitions, theorems, and lemmas"}
        )
        
        # Initialize embedding model
        if use_local_embeddings and USE_LOCAL_EMBEDDINGS:
            self.embedder = SentenceTransformer('all-MiniLM-L6-v2')
            self.use_local = True
        else:
            self.embedder = None
            self.use_local = False
            print("Using ChromaDB default embeddings")
    
    def generate_embedding(self, text: str) -> Optional[List[float]]:
        """Generate embedding for text."""
        if self.use_local:
            return self.embedder.encode(text).tolist()
        return None  # Let ChromaDB handle it
    
    def index_definitions(self, definitions: List[LeanDefinition], batch_size: int = 100):
        """Index definitions into the vector database."""
        for i in range(0, len(definitions), batch_size):
            batch = definitions[i:i + batch_size]
            
            ids = [d.get_id() for d in batch]
            
            # Prepare documents (text to embed)
            documents = []
            for d in batch:
                # Combine name, type, docstring, and content for embedding
                text_parts = [
                    f"{d.type} {d.name}",
                    d.docstring or "",
                    d.content
                ]
                documents.append("\n".join(filter(None, text_parts)))
            
            # Prepare metadata
            metadatas = [
                {
                    "name": d.name,
                    "type": d.type,
                    "file_path": d.file_path,
                    "line_number": d.line_number,
                    "module_path": d.module_path,
                    "has_docstring": d.docstring is not None
                }
                for d in batch
            ]
            
            # Generate embeddings if using local model
            if self.use_local:
                embeddings = [self.generate_embedding(doc) for doc in documents]
                self.collection.add(
                    ids=ids,
                    documents=documents,
                    metadatas=metadatas,
                    embeddings=embeddings
                )
            else:
                self.collection.add(
                    ids=ids,
                    documents=documents,
                    metadatas=metadatas
                )
            
            print(f"Indexed {len(batch)} definitions...")
    
    def search(self, 
               query: str, 
               n_results: int = 10,
               filter_type: Optional[str] = None,
               filter_module: Optional[str] = None) -> List[Dict]:
        """
        Search the vector database.
        
        Args:
            query: Natural language query
            n_results: Number of results to return
            filter_type: Filter by definition type (e.g., 'theorem', 'def')
            filter_module: Filter by module path prefix
        """
        where_clause = {}
        
        if filter_type:
            where_clause["type"] = filter_type
        
        if filter_module:
            where_clause["module_path"] = {"$contains": filter_module}
        
        results = self.collection.query(
            query_texts=[query],
            n_results=n_results,
            where=where_clause if where_clause else None
        )
        
        # Format results
        formatted_results = []
        for i in range(len(results['ids'][0])):
            formatted_results.append({
                'id': results['ids'][0][i],
                'document': results['documents'][0][i],
                'metadata': results['metadatas'][0][i],
                'distance': results['distances'][0][i] if 'distances' in results else None
            })
        
        return formatted_results

def crawl_mathlib(mathlib_path: str = "Mathlib") -> List[LeanDefinition]:
    """Crawl all Lean files in Mathlib and extract definitions."""
    parser = LeanParser()
    all_definitions = []
    
    mathlib_dir = Path(mathlib_path)
    if not mathlib_dir.exists():
        print(f"Error: {mathlib_path} does not exist")
        return all_definitions
    
    lean_files = list(mathlib_dir.rglob("*.lean"))
    print(f"Found {len(lean_files)} Lean files")
    
    for i, file_path in enumerate(lean_files):
        if i % 100 == 0:
            print(f"Processing file {i}/{len(lean_files)}: {file_path}")
        
        definitions = parser.parse_file(file_path)
        all_definitions.extend(definitions)
    
    return all_definitions

def main():
    """Main function to build the vector database."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Build Mathlib vector database")
    parser.add_argument("--mathlib-path", default="Mathlib", help="Path to Mathlib directory")
    parser.add_argument("--db-path", default="./mathlib_vectordb", help="Path for vector database")
    parser.add_argument("--limit", type=int, help="Limit number of files to process (for testing)")
    parser.add_argument("--search", help="Search query (if provided, search instead of indexing)")
    parser.add_argument("--filter-type", help="Filter search by type")
    parser.add_argument("--filter-module", help="Filter search by module")
    
    args = parser.parse_args()
    
    # Initialize vector database
    db = MathLibVectorDB(db_path=args.db_path, use_local_embeddings=USE_LOCAL_EMBEDDINGS)
    
    if args.search:
        # Search mode
        print(f"Searching for: {args.search}")
        results = db.search(
            args.search, 
            filter_type=args.filter_type,
            filter_module=args.filter_module
        )
        
        for i, result in enumerate(results, 1):
            print(f"\n--- Result {i} ---")
            print(f"Name: {result['metadata']['name']}")
            print(f"Type: {result['metadata']['type']}")
            print(f"File: {result['metadata']['file_path']}:{result['metadata']['line_number']}")
            print(f"Module: {result['metadata']['module_path']}")
            if result['distance']:
                print(f"Distance: {result['distance']:.4f}")
            print(f"Preview: {result['document'][:200]}...")
    else:
        # Indexing mode
        print("Starting Mathlib extraction...")
        
        # Crawl and parse Mathlib
        definitions = crawl_mathlib(args.mathlib_path)
        
        if args.limit:
            definitions = definitions[:args.limit]
        
        print(f"\nExtracted {len(definitions)} definitions")
        
        # Index into vector database
        print("\nIndexing into vector database...")
        db.index_definitions(definitions)
        
        print(f"\nVector database created at: {args.db_path}")
        print(f"Total definitions indexed: {len(definitions)}")
        
        # Print statistics
        type_counts = {}
        for d in definitions:
            type_counts[d.type] = type_counts.get(d.type, 0) + 1
        
        print("\nDefinition types:")
        for def_type, count in sorted(type_counts.items()):
            print(f"  {def_type}: {count}")

if __name__ == "__main__":
    main()