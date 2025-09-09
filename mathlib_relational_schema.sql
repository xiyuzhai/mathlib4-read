-- Relational Database Schema for Mathlib Content
-- Manual extraction and annotation system

-- Main definitions table
CREATE TABLE definitions (
    id INTEGER PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    type VARCHAR(50) NOT NULL, -- 'class', 'theorem', 'lemma', 'def', 'instance', 'structure'
    file_path VARCHAR(500) NOT NULL,
    line_number INTEGER NOT NULL,
    module_path VARCHAR(500) NOT NULL,
    -- Key properties
    extends VARCHAR(500), -- for classes: what it extends
    parameters TEXT, -- type parameters
    return_type VARCHAR(255),
    is_notation_class BOOLEAN DEFAULT FALSE,
    is_to_additive BOOLEAN DEFAULT FALSE,
    priority INTEGER, -- instance priority if applicable
    UNIQUE(file_path, name, line_number)
);

-- Natural language annotations for RAG
CREATE TABLE nl_annotations (
    id INTEGER PRIMARY KEY,
    definition_id INTEGER NOT NULL,
    annotation_type VARCHAR(50), -- 'summary', 'intuition', 'usage', 'example'
    content TEXT NOT NULL,
    FOREIGN KEY (definition_id) REFERENCES definitions(id)
);

-- Properties and constraints
CREATE TABLE properties (
    id INTEGER PRIMARY KEY,
    definition_id INTEGER NOT NULL,
    property_name VARCHAR(255) NOT NULL,
    property_value TEXT,
    property_type VARCHAR(50), -- 'axiom', 'field', 'constraint', 'relation'
    FOREIGN KEY (definition_id) REFERENCES definitions(id)
);

-- Dependencies and imports
CREATE TABLE dependencies (
    id INTEGER PRIMARY KEY,
    from_definition_id INTEGER NOT NULL,
    to_module VARCHAR(500), -- imported module
    dependency_type VARCHAR(50), -- 'import', 'extends', 'uses'
    FOREIGN KEY (from_definition_id) REFERENCES definitions(id)
);

-- Docstrings and comments
CREATE TABLE documentation (
    id INTEGER PRIMARY KEY,
    definition_id INTEGER NOT NULL,
    doc_type VARCHAR(50), -- 'docstring', 'note', 'tag'
    content TEXT,
    FOREIGN KEY (definition_id) REFERENCES definitions(id)
);

-- Relationships between definitions
CREATE TABLE relationships (
    id INTEGER PRIMARY KEY,
    from_id INTEGER NOT NULL,
    to_id INTEGER NOT NULL,
    relationship_type VARCHAR(50), -- 'extends', 'instance_of', 'uses', 'generalizes'
    FOREIGN KEY (from_id) REFERENCES definitions(id),
    FOREIGN KEY (to_id) REFERENCES definitions(id)
);

-- Search index for filtering
CREATE TABLE search_tags (
    id INTEGER PRIMARY KEY,
    definition_id INTEGER NOT NULL,
    tag VARCHAR(100) NOT NULL,
    tag_category VARCHAR(50), -- 'domain', 'technique', 'structure'
    FOREIGN KEY (definition_id) REFERENCES definitions(id)
);

-- Create indexes for common queries
CREATE INDEX idx_definitions_type ON definitions(type);
CREATE INDEX idx_definitions_module ON definitions(module_path);
CREATE INDEX idx_nl_annotations_def ON nl_annotations(definition_id);
CREATE INDEX idx_properties_def ON properties(definition_id);
CREATE INDEX idx_search_tags_def ON search_tags(definition_id);
CREATE INDEX idx_search_tags_tag ON search_tags(tag);