-- Example queries for the Mathlib relational database

-- 1. Find all norm-related classes
SELECT d.name, d.type, na.content as summary
FROM definitions d
LEFT JOIN nl_annotations na ON d.id = na.definition_id AND na.annotation_type = 'summary'
WHERE d.name LIKE '%Norm%'
ORDER BY d.line_number;

-- 2. Get all classes that extend Norm
SELECT d.name, d.extends, doc.content as documentation
FROM definitions d
LEFT JOIN documentation doc ON d.id = doc.definition_id
WHERE d.extends LIKE '%Norm%';

-- 3. Find theorems and lemmas about convexity (would need to be populated)
SELECT d.name, d.type, d.file_path, d.line_number
FROM definitions d
JOIN search_tags st ON d.id = st.definition_id
WHERE st.tag = 'convex' AND d.type IN ('theorem', 'lemma');

-- 4. Get hierarchy of normed structures
WITH RECURSIVE hierarchy AS (
    -- Base case: start with Norm
    SELECT d.id, d.name, d.extends, 0 as level
    FROM definitions d
    WHERE d.name = 'Norm'
    
    UNION ALL
    
    -- Recursive case: find what extends current level
    SELECT d.id, d.name, d.extends, h.level + 1
    FROM definitions d
    JOIN hierarchy h ON d.extends LIKE '%' || h.name || '%'
)
SELECT level, name, extends
FROM hierarchy
ORDER BY level, name;

-- 5. Find all definitions with natural language annotations about Banach spaces
SELECT d.name, d.type, na.content
FROM definitions d
JOIN nl_annotations na ON d.id = na.definition_id
WHERE na.content LIKE '%Banach%';

-- 6. Get all properties of SeminormedAddGroup
SELECT p.property_name, p.property_value, p.property_type
FROM properties p
JOIN definitions d ON p.definition_id = d.id
WHERE d.name = 'SeminormedAddGroup';

-- 7. Find definitions by module with specific tags
SELECT d.name, d.type, GROUP_CONCAT(st.tag) as tags
FROM definitions d
JOIN search_tags st ON d.id = st.definition_id
WHERE d.module_path LIKE 'Mathlib.Analysis.Normed%'
GROUP BY d.id, d.name, d.type;

-- 8. Get documentation and intuition for a specific concept
SELECT 
    d.name,
    doc.content as documentation,
    na_summary.content as summary,
    na_intuition.content as intuition,
    na_usage.content as usage_notes
FROM definitions d
LEFT JOIN documentation doc ON d.id = doc.definition_id
LEFT JOIN nl_annotations na_summary ON d.id = na_summary.definition_id 
    AND na_summary.annotation_type = 'summary'
LEFT JOIN nl_annotations na_intuition ON d.id = na_intuition.definition_id 
    AND na_intuition.annotation_type = 'intuition'
LEFT JOIN nl_annotations na_usage ON d.id = na_usage.definition_id 
    AND na_usage.annotation_type = 'usage'
WHERE d.name = 'NormedGroup';

-- 9. Find all @[to_additive] marked definitions
SELECT name, type, line_number
FROM definitions
WHERE is_to_additive = TRUE
ORDER BY line_number;

-- 10. Complex query: Find related definitions through relationships
SELECT 
    d1.name as from_def,
    r.relationship_type,
    d2.name as to_def,
    d2.type as to_type
FROM relationships r
JOIN definitions d1 ON r.from_id = d1.id
JOIN definitions d2 ON r.to_id = d2.id
WHERE d1.name IN ('SeminormedGroup', 'NormedGroup')
ORDER BY d1.name, r.relationship_type;