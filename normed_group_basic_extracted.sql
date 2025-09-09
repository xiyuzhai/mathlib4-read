-- Manual extraction from Mathlib/Analysis/Normed/Group/Basic.lean
-- This demonstrates the structured data extraction process

-- Clear existing data (for demo)
DELETE FROM definitions WHERE file_path = 'Mathlib/Analysis/Normed/Group/Basic.lean';

-- Core Norm Classes
INSERT INTO definitions (name, type, file_path, line_number, module_path, extends, parameters, is_notation_class) VALUES
('Norm', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 52, 'Mathlib.Analysis.Normed.Group.Basic', NULL, 'E : Type*', TRUE),
('NNNorm', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 58, 'Mathlib.Analysis.Normed.Group.Basic', NULL, 'E : Type*', TRUE),
('ENorm', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 64, 'Mathlib.Analysis.Normed.Group.Basic', NULL, 'E : Type*', TRUE);

-- Extended Norm Classes
INSERT INTO definitions (name, type, file_path, line_number, module_path, extends, parameters) VALUES
('ContinuousENorm', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 100, 'Mathlib.Analysis.Normed.Group.Basic', 'ENorm E', 'E : Type* [TopologicalSpace E]', FALSE),
('ESeminormedAddMonoid', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 106, 'Mathlib.Analysis.Normed.Group.Basic', 'ContinuousENorm E, AddMonoid E', 'E : Type* [TopologicalSpace E]', FALSE),
('ENormedAddMonoid', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 114, 'Mathlib.Analysis.Normed.Group.Basic', 'ESeminormedAddMonoid E', 'E : Type* [TopologicalSpace E]', FALSE),
('ESeminormedMonoid', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 121, 'Mathlib.Analysis.Normed.Group.Basic', 'ContinuousENorm E, Monoid E', 'E : Type* [TopologicalSpace E]', FALSE),
('ENormedMonoid', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 129, 'Mathlib.Analysis.Normed.Group.Basic', 'ESeminormedMonoid E', 'E : Type* [TopologicalSpace E]', FALSE);

-- Seminormed and Normed Groups
INSERT INTO definitions (name, type, file_path, line_number, module_path, extends, parameters, is_to_additive) VALUES
('SeminormedAddGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 163, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, AddGroup E, PseudoMetricSpace E', 'E : Type*', FALSE),
('SeminormedGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 171, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, Group E, PseudoMetricSpace E', 'E : Type*', TRUE),
('NormedAddGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 178, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, AddGroup E, MetricSpace E', 'E : Type*', FALSE),
('NormedGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 186, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, Group E, MetricSpace E', 'E : Type*', TRUE),
('SeminormedAddCommGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 193, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, AddCommGroup E, PseudoMetricSpace E', 'E : Type*', FALSE),
('SeminormedCommGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 202, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, CommGroup E, PseudoMetricSpace E', 'E : Type*', TRUE),
('NormedAddCommGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 209, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, AddCommGroup E, MetricSpace E', 'E : Type*', FALSE),
('NormedCommGroup', 'class', 'Mathlib/Analysis/Normed/Group/Basic.lean', 217, 'Mathlib.Analysis.Normed.Group.Basic', 'Norm E, CommGroup E, MetricSpace E', 'E : Type*', TRUE);

-- Get the IDs for reference (in practice, would query)
-- Assuming Norm has id=1, NNNorm=2, ENorm=3, etc.

-- Natural Language Annotations
INSERT INTO nl_annotations (definition_id, annotation_type, content) VALUES
(1, 'summary', 'Base class providing a real-valued norm function for a type'),
(1, 'intuition', 'Measures the "size" or "length" of elements in a mathematical structure'),
(1, 'usage', 'Foundation for normed spaces, used with notation ‖x‖'),

(2, 'summary', 'Non-negative real-valued norm function'),
(2, 'intuition', 'Ensures norm values are always non-negative by type construction'),
(2, 'usage', 'Used when you need guaranteed non-negative norms, notation ‖x‖₊'),

(3, 'summary', 'Extended non-negative real-valued norm allowing infinity'),
(3, 'intuition', 'Handles potentially infinite norms in extended metric spaces'),
(3, 'usage', 'For spaces where elements can have infinite distance/norm'),

(10, 'summary', 'Additive group with norm inducing a metric via dist(x,y) = ‖x-y‖'),
(10, 'intuition', 'Combines group structure with metric geometry through the norm'),
(10, 'usage', 'Foundation for Banach spaces and functional analysis'),

(11, 'summary', 'Multiplicative group with norm inducing a metric via dist(x,y) = ‖x/y‖'),
(11, 'intuition', 'Multiplicative version where distance is measured by division'),
(11, 'usage', 'For multiplicative structures in analysis');

-- Properties
INSERT INTO properties (definition_id, property_name, property_value, property_type) VALUES
(1, 'norm', 'E → ℝ', 'field'),
(2, 'nnnorm', 'E → ℝ≥0', 'field'),
(3, 'enorm', 'E → ℝ≥0∞', 'field'),

(5, 'enorm_zero', '‖(0 : E)‖ₑ = 0', 'axiom'),
(5, 'enorm_add_le', '∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ', 'axiom'),

(10, 'dist', 'fun x y => ‖x - y‖', 'field'),
(10, 'dist_eq', '∀ x y, dist x y = ‖x - y‖', 'axiom'),

(11, 'dist', 'fun x y => ‖x / y‖', 'field'),
(11, 'dist_eq', '∀ x y, dist x y = ‖x / y‖', 'axiom');

-- Dependencies
INSERT INTO dependencies (from_definition_id, to_module, dependency_type) VALUES
(1, 'Mathlib.Analysis.Normed.Group.Seminorm', 'import'),
(1, 'Mathlib.Data.NNReal.Basic', 'import'),
(1, 'Mathlib.Topology.MetricSpace.Basic', 'import');

-- Documentation
INSERT INTO documentation (definition_id, doc_type, content) VALUES
(1, 'docstring', 'Auxiliary class, endowing a type E with a function norm : E → ℝ with notation ‖x‖. This class is designed to be extended in more interesting classes specifying the properties of the norm.'),
(2, 'docstring', 'Auxiliary class, endowing a type α with a function nnnorm : α → ℝ≥0 with notation ‖x‖₊'),
(10, 'docstring', 'A seminormed group is an additive group endowed with a norm for which dist x y = ‖x - y‖ defines a pseudometric space structure.');

-- Relationships
INSERT INTO relationships (from_id, to_id, relationship_type) VALUES
(5, 4, 'extends'), -- ESeminormedAddMonoid extends ContinuousENorm
(6, 5, 'extends'), -- ENormedAddMonoid extends ESeminormedAddMonoid
(10, 1, 'extends'), -- SeminormedAddGroup extends Norm
(11, 1, 'extends'), -- SeminormedGroup extends Norm
(12, 10, 'generalizes'), -- NormedAddGroup generalizes SeminormedAddGroup
(13, 11, 'generalizes'); -- NormedGroup generalizes SeminormedGroup

-- Search Tags
INSERT INTO search_tags (definition_id, tag, tag_category) VALUES
(1, 'norm', 'structure'),
(1, 'metric', 'domain'),
(1, 'analysis', 'domain'),
(10, 'group', 'structure'),
(10, 'seminorm', 'structure'),
(10, 'pseudometric', 'structure'),
(10, 'functional-analysis', 'domain'),
(11, 'multiplicative', 'structure'),
(12, 'banach', 'domain'),
(12, 'complete', 'structure');