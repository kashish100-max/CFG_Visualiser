# CFG Visualizer — Context-Free Grammar Derivation & Parse Tree Generator
It is an interactive web-based tool designed to help students understand Context-Free Grammars (CFGs) through visualization and step-by-step derivations.

# Features
## 1. Grammar Input System
->Accepts CFG rules in structured format (S -> aSb | ab)
->Supports multiple productions and alternatives
->Detects invalid grammar formats

## 2. String Validation
->Users input a target string
->System verifies whether it can be derived from the grammar
->Provides detailed failure analysis if not derivable

## 3. Leftmost & Rightmost Derivation
->Generates:
    ->Leftmost Derivation (LMD)
    ->Rightmost Derivation (RMD)
->Step-by-step expansion with highlighted symbols

## 4. Parse Tree Visualization
->Automatically constructs parse trees
->Interactive, animated tree rendering Shows:
    ->Parent-child relationships
    ->Symbol expansion flow

## 5. Ambiguity Detection
->Detects if grammar is ambiguous
->Generates multiple parse trees for the same string
->Allows comparison between trees

## 6. Smart Error Analysis
->When derivation fails, the system explains why:
   ->Unreachable non-terminals
   ->Non-productive symbols
   ->Prefix mismatches
   ->Invalid grammar structures

## 7. Auto String Generation
->Suggests a valid string if the given one cannot be derived
->Helps debug grammar issues

## 8. Interactive UI
->Animated transitions
->Step navigation controls (Play / Pause / Step)
->Responsive design (mobile + desktop)
->Visual highlighting of terminals and non-terminals