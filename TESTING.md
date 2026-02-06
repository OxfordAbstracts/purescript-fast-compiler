# Testing Strategy

## Overview

The PureScript parser includes comprehensive testing at multiple levels to ensure correctness and robustness.

## Test Categories

### 1. Unit Tests

Basic functionality tests for individual components:

- **Keywords**: Verifies all PureScript keywords are recognized
- **Identifiers**: Tests lowercase, uppercase, and operator identifiers
- **Literals**: Validates integers, floats, strings, characters, booleans
- **Comments**: Tests line comments, block comments, and nested block comments
- **Operators**: Ensures operator tokenization with correct precedence

```bash
cargo test test_keywords
cargo test test_identifiers
# etc.
```

### 2. Fuzz/Property Tests

**Critical invariant**: All tokens, when concatenated via their source spans, should exactly reconstruct the original source text (minus intentionally skipped whitespace).

#### Property Tests Included

1. **`prop_lex_identifiers_roundtrip`**
   - Generates random valid PureScript identifiers
   - Lexes them and reconstructs from spans
   - Verifies reconstruction equals original

2. **`prop_lex_never_panics`**
   - Generates arbitrary expressions
   - Ensures lexer never panics (graceful error handling)

3. **`prop_spans_are_valid`**
   - Verifies all span positions are within source bounds
   - Ensures `span.start <= span.end`
   - Checks no out-of-bounds access

4. **`prop_spans_cover_source`**
   - Generates sequences of expressions
   - Verifies all non-whitespace characters are covered by token spans
   - Ensures no characters are silently dropped

#### Example Property Test Output

```rust
// Input
"factorial n = n * factorial (n - 1)"

// Property: Concatenating source[token.span] reconstructs original
let reconstructed = tokens.iter()
    .map(|(_, span)| &source[span.start..span.end])
    .collect::<String>();

assert_eq!(reconstructed, original); // ✓ PASS
```

### 3. Integration Tests

**`test_token_roundtrip_simple`**: Comprehensive roundtrip tests on real PureScript code:

```purescript
- "module Main where"
- "factorial n = n * factorial (n - 1)"
- "let x = 42 in x + 1"
- "data Maybe a = Just a | Nothing"
- "import Data.Array (head, tail)"
```

Verifies for each:
- ✓ Lexing succeeds
- ✓ Spans are sequential (no overlaps)
- ✓ Reconstruction matches original

**`test_no_dropped_characters`**: Comprehensive test on multi-line module:
- Full PureScript module with imports, functions, comments
- Verifies every non-whitespace character is covered by exactly one token
- Ensures no silent data loss

## Running Tests

### All tests
```bash
cargo test
```

### Only unit tests
```bash
cargo test --lib test_
```

### Only property tests (with more cases)
```bash
PROPTEST_CASES=1000 cargo test --lib prop_
```

### Specific test
```bash
cargo test test_token_roundtrip_simple -- --nocapture
```

## Test Coverage

Current coverage (Phase 1):
- **14 tests total**
- 6 unit tests (basic functionality)
- 4 property/fuzz tests (invariant checking)
- 2 integration tests (real-world scenarios)
- 2 auxiliary tests (arena, layout stubs)

## Why These Tests Matter

### Correctness Guarantees

1. **No Silent Data Loss**: Property tests ensure no characters are dropped
2. **Precise Position Tracking**: Span tests verify accurate error reporting
3. **Robustness**: Fuzz tests ensure no panics on arbitrary input
4. **Regression Prevention**: Integration tests catch breaking changes

### Property-Based Testing Advantages

Traditional tests check specific inputs:
```rust
assert_eq!(lex("foo").unwrap()[0], Token::Ident);
```

Property tests check universal invariants across thousands of inputs:
```rust
proptest! {
    // For ALL valid identifiers...
    fn prop(ident in arb_ident()) {
        // ...roundtrip must succeed
        assert_eq!(reconstruct(lex(ident)), ident);
    }
}
```

## Future Test Additions

As we move through implementation phases:

- **Phase 2**: Layout processing property tests
- **Phase 3**: Parser invariant tests (AST structure)
- **Phase 4**: Operator precedence/associativity tests
- **Phase 5**: Type checking property tests
- **Phase 7**: Performance benchmarks
- **Phase 8**: Error message quality tests

## Continuous Integration

Tests run automatically on every commit. All tests must pass before merging.

```bash
# Pre-commit hook recommendation
cargo test --lib && cargo clippy -- -D warnings
```
