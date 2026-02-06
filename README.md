# PureScript Fast Compiler

A production-grade, high-performance parser for the PureScript programming language, written in Rust.

## Architecture

Three-stage parsing pipeline optimized for performance:

1. **Logos Lexer** - Fast regex-based tokenization (~10x faster than hand-written)
2. **Layout Processor** - Converts indentation-sensitive syntax to layout tokens
3. **LALRPOP Parser** - Grammar-based parser with declarative operator precedence

### Performance Features

- **String Interning** - Deduplicates identifiers for O(1) equality checks
- **Arena Allocation** - Batch allocation for AST nodes (better cache locality)
- **Zero-copy Lexing** - Uses string slices instead of copying
- **Token Stream Buffering** - Reduces allocator pressure

## Current Status

### Phase 1: Fast Lexer Foundation ✅ COMPLETE

- [x] Complete PureScript token definitions
- [x] Logos-based lexer with regex patterns
- [x] Position tracking (spans)
- [x] Nested block comment handling
- [x] String escape sequence parsing
- [x] String interning for identifiers
- [x] Arena allocator setup
- [x] Comprehensive tests

### Upcoming Phases

- **Phase 2**: Layout Processing (indentation-sensitive syntax)
- **Phase 3**: Core Parser & AST (MVP milestone)
- **Phase 4**: Operator Precedence
- **Phase 5**: Type System
- **Phase 6**: Module System & Advanced Features
- **Phase 7**: Performance Optimization
- **Phase 8**: Production Polish

## Usage

### Lexing a PureScript file

```bash
cargo run test.purs
```

### Running tests

```bash
# All tests (14 tests including property/fuzz tests)
cargo test

# Run property tests with more iterations
PROPTEST_CASES=1000 cargo test prop_

# See detailed test documentation
cat TESTING.md
```

**Test Coverage**:
- ✅ 6 unit tests (keywords, identifiers, literals, operators, comments)
- ✅ 4 property/fuzz tests (roundtrip invariants, span validity, no panics)
- ✅ 2 integration tests (real PureScript code, comprehensive coverage)
- ✅ 2 auxiliary tests (arena allocation, layout stubs)

**Key Property**: All tokens preserve source text - concatenating `source[token.span]` for all tokens exactly reconstructs the original (minus intentionally skipped whitespace). This is verified through fuzz testing.

### Building

```bash
cargo build --release
```

## Example

Input (`test.purs`):
```purescript
module Main where

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)
```

Output:
```
Lexed 26 tokens:
   0: Module @ 0..6
   1: UpperIdent(Main) @ 7..11
   2: Where @ 12..17
   3: LowerIdent(factorial) @ 19..28
   4: DoubleColon @ 29..31
   5: UpperIdent(Int) @ 32..35
   6: Arrow @ 36..38
   ...
```

## Dependencies

- **logos** - Fast lexer generation
- **string-interner** - String deduplication
- **bumpalo** - Arena allocation
- **lalrpop** - Parser generation
- **miette** - Beautiful error messages
- **thiserror** - Error handling

## Performance Targets

- Parse 50,000+ lines/sec on typical PureScript code
- Memory usage < 10MB for 10,000-line file
- Sub-100ms parse time for typical modules

## License

MIT

## Contributing

This is a work in progress. Contributions welcome!
