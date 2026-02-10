# Migration Plan: Replace `id-arena::Id` with Custom Identifier Types

## Overview

**For 0.8.0 Breaking Release**: Replace `id-arena` entirely with specialized arena and identifier types that provide:
- Full control over implementation
- Native `rkyv` serialization support
- Maximum type safety with specialized types for each use case
- Cleaner, more ergonomic API
- No external dependencies for arena management

## Problem Statement

Currently, the codebase uses `id-arena::Arena<T>` and `id-arena::Id<T>` throughout the CFG, TAC, and SSA intermediate representations. The `id-arena` crate doesn't provide `rkyv` serialization support out of the box, and we need full control over both the identifier types and arena storage.

**Note**: This is a **breaking change** for the 0.8.0 release. We will **completely remove the `id-arena` dependency** and replace it with specialized types:
- `BlockArena` + `BlockId` (not `Arena<Block>`)
- `TBlockArena` + `TBlockId` (not `Arena<TBlock>`)
- `SBlockArena` + `SBlockId`, `SValueArena` + `SValueId` (not generic arenas)
- etc.

## Affected Crates

Based on the analysis, the following crates use `id-arena`:

1. **swc-cfg**: Control Flow Graph representation
   - `Id<Block>` - Block identifiers
   - `Arena<Block>` - Block storage

2. **swc-tac**: Three-Address Code representation
   - `Id<TBlock>` - TAC block identifiers
   - `Arena<TBlock>` - TAC block storage

3. **swc-ssa**: Static Single Assignment representation
   - `Id<SBlock>` - SSA block identifiers
   - `Id<SValueW>` - SSA value identifiers
   - `Arena<SBlock>` - SSA block storage
   - `Arena<SValueW>` - SSA value storage

4. **swc-opt-ssa**: Optimized SSA representation
   - `Id<OptBlock>` - Optimized block identifiers
   - `Id<OptValueW>` - Optimized value identifiers
   - `Arena<OptBlock>`, `Arena<OptValueW>` - Storage

5. **swc-ll-common**: Low-level common utilities
   - Used in trait definitions and utilities

## Key Types Using Id<T>

### CFG (swc-cfg)
- `Func::entry: Id<Block>`
- `Cfg::blocks: Arena<Block>`
- `Term` variants contain `Id<Block>`
- `Catch::Jump { k: Id<Block> }`

### TAC (swc-tac)
- `TFunc::entry: Id<TBlock>`
- `TCfg::blocks: Arena<TBlock>`
- `TPostcedent`, `TTerm`, `TCatch` use `Id<TBlock>`

### SSA (swc-ssa)
- `SFunc::entry: Id<SBlock>`
- `SCfg::blocks: Arena<SBlock>`
- `SCfg::values: Arena<SValueW>`
- `SBlock::params: Vec<(Id<SValueW>, ())>`
- `SBlock::stmts: Vec<Id<SValueW>>`
- `SValue`, `SPostcedent`, `STerm`, `STarget`, `SCatch` use `Id<SValueW>` and `Id<SBlock>`

### Opt-SSA (swc-opt-ssa)
- `OptFunc::entry: Id<OptBlock>`
- `OptCfg::values: Arena<OptValueW>`
- `OptCfg::blocks: Arena<OptBlock>`
- `OptBlock::params: Vec<(Id<OptValueW>, ...)>`
- Similar patterns to SSA

## Migration Strategy

### Phase 1: Create Specialized Arena and Identifier Infrastructure

**Approach**: Create specialized arena AND identifier types for each use case. Each `Arena<T>` becomes its own distinct type (e.g., `BlockArena`, not `Arena<Block>`).

**Location**: Define types in their corresponding crates using a macro from `swc-ll-common`.

1. **Create a macro for generating paired Arena+ID types** (in `swc-ll-common`):
   ```rust
   // In swc-ll-common/src/lib.rs
   
   /// Macro to generate a specialized arena type and its corresponding ID type.
   /// 
   /// This creates:
   /// - A specialized arena type (e.g., `BlockArena`)
   /// - A specialized ID type (e.g., `BlockId`)
   /// - All necessary trait implementations
   /// 
   /// Example: `define_arena!(pub BlockArena, BlockId for Block);`
   #[macro_export]
   macro_rules! define_arena {
       ($arena_vis:vis $arena_name:ident, $id_vis:vis $id_name:ident for $item_type:ty) => {
           // The specialized ID type
           #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
           #[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
           #[repr(transparent)]
           $id_vis struct $id_name(usize);
           
           impl $id_name {
               /// Create a new ID from a raw index.
               #[inline]
               pub fn new(index: usize) -> Self {
                   Self(index)
               }
               
               /// Get the raw index value.
               #[inline]
               pub fn index(self) -> usize {
                   self.0
               }
           }
           
           // The specialized Arena type
           #[derive(Debug, Clone, PartialEq, Eq)]
           #[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
           $arena_vis struct $arena_name {
               items: Vec<$item_type>,
           }
           
           impl $arena_name {
               /// Create a new empty arena.
               #[inline]
               pub fn new() -> Self {
                   Self { items: Vec::new() }
               }
               
               /// Allocate a value in the arena and return its ID.
               #[inline]
               pub fn alloc(&mut self, value: $item_type) -> $id_name {
                   let index = self.items.len();
                   self.items.push(value);
                   $id_name(index)
               }
               
               /// Get a reference to a value by ID.
               #[inline]
               pub fn get(&self, id: $id_name) -> Option<&$item_type> {
                   self.items.get(id.0)
               }
               
               /// Get a mutable reference to a value by ID.
               #[inline]
               pub fn get_mut(&mut self, id: $id_name) -> Option<&mut $item_type> {
                   self.items.get_mut(id.0)
               }
               
               /// Iterate over all (ID, value) pairs.
               #[inline]
               pub fn iter(&self) -> impl Iterator<Item = ($id_name, &$item_type)> {
                   self.items.iter().enumerate().map(|(idx, item)| ($id_name(idx), item))
               }
               
               /// Iterate mutably over all (ID, value) pairs.
               #[inline]
               pub fn iter_mut(&mut self) -> impl Iterator<Item = ($id_name, &mut $item_type)> {
                   self.items.iter_mut().enumerate().map(|(idx, item)| ($id_name(idx), item))
               }
               
               /// Get the number of items in the arena.
               #[inline]
               pub fn len(&self) -> usize {
                   self.items.len()
               }
               
               /// Check if the arena is empty.
               #[inline]
               pub fn is_empty(&self) -> bool {
                   self.items.is_empty()
               }
           }
           
           impl Default for $arena_name {
               fn default() -> Self {
                   Self::new()
               }
           }
           
           // Indexing support
           impl std::ops::Index<$id_name> for $arena_name {
               type Output = $item_type;
               
               #[inline]
               fn index(&self, id: $id_name) -> &Self::Output {
                   &self.items[id.0]
               }
           }
           
           impl std::ops::IndexMut<$id_name> for $arena_name {
               #[inline]
               fn index_mut(&mut self, id: $id_name) -> &mut Self::Output {
                   &mut self.items[id.0]
               }
           }
           
           // arena-traits support
           impl arena_traits::IndexAlloc<$item_type> for $arena_name {
               type Id = $id_name;
               
               #[inline]
               fn alloc(&mut self, value: $item_type) -> $id_name {
                   $arena_name::alloc(self, value)
               }
           }
       };
   }
   ```

2. **Define specialized Arena+ID pairs in each crate**:
   ```rust
   // In swc-ll-common/src/lib.rs
   
   /// Macro to generate arena ID types with consistent implementations
   #[macro_export]
   macro_rules! define_arena_id {
       ($vis:vis $name:ident for $arena_type:ty) => {
           #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
           #[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
           #[repr(transparent)]
           $vis struct $name(usize);
           
           impl $name {
               /// Create a new ID from a raw index.
               #[inline]
               pub fn new(index: usize) -> Self {
                   Self(index)
               }
               
               /// Get the raw index value.
               #[inline]
               pub fn index(self) -> usize {
                   self.0
               }
           }
           
           // Arena indexing support
           impl std::ops::Index<$name> for $crate::Arena<$arena_type> {
               type Output = $arena_type;
               
               #[inline]
               fn index(&self, id: $name) -> &Self::Output {
                   &self.items[id.0]
               }
           }
           
           impl std::ops::IndexMut<$name> for $crate::Arena<$arena_type> {
               #[inline]
               fn index_mut(&mut self, id: $name) -> &mut Self::Output {
                   &mut self.items[id.0]
               }
           }
           
           // arena-traits support
           impl arena_traits::IndexAlloc<$arena_type> for $crate::Arena<$arena_type> {
               type Id = $name;
               
               #[inline]
               fn alloc(&mut self, value: $arena_type) -> $name {
                   $name($crate::Arena::alloc(self, value))
               }
           }
       };
   }
   ```

2. **Define specialized ID types in each crate**:

   ```rust
   // In swc-cfg/src/lib.rs
   use swc_ll_common::define_arena_id;
   
   define_arena_id!(pub BlockId for Block);
   ```

   ```rust
   // In swc-tac/src/lib.rs
   define_arena_id!(pub TBlockId for TBlock);
   ```

   ```rust
   // In swc-ssa/src/lib.rs
   define_arena_id!(pub SBlockId for SBlock);
   define_arena_id!(pub SValueId for SValueW);
   ```

   ```rust
   // In swc-opt-ssa/src/lib.rs
   define_arena_id!(pub OptBlockId for OptBlock);
   define_arena_id!(pub OptValueId for OptValueW);
   ```

3. **All trait implementations included in macro**: The macro provides everything needed (indexing, arena-traits support, rkyv derives).

### Phase 2: Update Type Signatures (Per Crate)

For each crate, update in this order:

#### 2.1 swc-cfg
- [ ] Define `BlockArena` and `BlockId` using macro
- [ ] Replace `id_arena::Arena<Block>` with `BlockArena` in:
  - `Cfg::blocks` field
  - All method signatures
- [ ] Replace `id_arena::Id<Block>` with `BlockId` in:
  - `Func::entry` field
  - `Term` enum variants
  - `Catch` enum variants
  - `recfg` module
  - `simplify` module
  - `to_cfg` module

#### 2.2 swc-tac
- [ ] Define `TBlockArena` and `TBlockId` using macro
- [ ] Replace `id_arena::Arena<TBlock>` with `TBlockArena` in:
  - `TCfg::blocks` field
  - All method signatures
- [ ] Replace `id_arena::Id<TBlock>` with `TBlockId` in:
  - `TFunc::entry` field
  - `TPostcedent`, `TTerm`, `TCatch` types
  - `conv` module
  - `rew` module
  - `prepa` module
  - `consts` module
  - `lam` module

#### 2.3 swc-ssa
- [ ] Define `SBlockArena`, `SBlockId`, `SValueArena`, `SValueId` using macro
- [ ] Replace `id_arena::Arena<SBlock>` with `SBlockArena` in:
  - `SCfg::blocks` field
- [ ] Replace `id_arena::Arena<SValueW>` with `SValueArena` in:
  - `SCfg::values` field
- [ ] Replace `id_arena::Id<SBlock>` with `SBlockId` and `id_arena::Id<SValueW>` with `SValueId` in:
  - `SFunc::entry` field
  - `SBlock::params` and `SBlock::stmts` fields
  - `SValue` enum variants
  - `SPostcedent`, `STerm`, `STarget`, `SCatch` types
  - `conv` module
  - `rew` module
  - `simplify` module
  - `impls` module
  - `opt_stub` module
  - `consts` module

#### 2.4 swc-opt-ssa
- [ ] Define `OptBlockArena`, `OptBlockId`, `OptValueArena`, `OptValueId` using macro
- [ ] Replace `id_arena::Arena<OptBlock>` with `OptBlockArena`
- [ ] Replace `id_arena::Arena<OptValueW>` with `OptValueArena`
- [ ] Replace `id_arena::Id<OptBlock>` with `OptBlockId` and `id_arena::Id<OptValueW>` with `OptValueId` in:
  - `OptFunc::entry` field
  - `OptCfg` fields
  - `OptBlock::params` field
  - `OptValue` enum variants
  - Related types and modules

#### 2.5 swc-ll-common
- [ ] Update trait definitions and implementations to use generic identifiers
- [ ] Ensure `ItemGetter` and `ItemGetterExt` work with new types

### Phase 3: Update Conversions and Implementations

- [ ] Update `From`/`Into` implementations between representations
- [ ] Update `Default` implementations
- [ ] Update `TryFrom` implementations for conversions between CFG/TAC/SSA
- [ ] Ensure all arena allocations use the correct type

### Phase 4: Update Arena Usage Patterns

Migrate from `id_arena` patterns to specialized arenas:
- [ ] Replace `id_arena::Arena::alloc()` → `BlockArena::alloc()`, etc.
- [ ] Update indexing: automatic via specialized types (e.g., `block_arena[block_id]`)
- [ ] Update iteration: `arena.iter()` now returns `(BlockId, &Block)` pairs
- [ ] Remove all `use id_arena::*` imports
- [ ] No generic `Arena<T>` imports needed - use specific types

### Phase 5: Remove id-arena Dependency

- [ ] Remove `id-arena` from `Cargo.toml` workspace dependencies
- [ ] Remove `id-arena` from individual crate dependencies
- [ ] Verify no remaining references to `id_arena` in codebase
- [ ] Update `arena-traits` configuration if needed

### Phase 6: Testing and Validation

- [ ] Run existing tests to ensure no regressions
- [ ] Add specific tests for rkyv serialization/deserialization
- [ ] Verify arena operations work correctly
- [ ] Test conversions between different IR levels
- [ ] Performance benchmarks (if available)

## Implementation Notes

### Why Specialized Types instead of Generic ArenaId<T>?

1. **Stronger Type Safety**: `BlockId` and `TBlockId` are completely incompatible types - no possibility of mixing
2. **Better Type Errors**: Error messages show concrete types like `BlockId` instead of `ArenaId<Block>`
3. **Simpler Mental Model**: No generic parameters to reason about
4. **Cleaner API**: `pub entry: BlockId` is clearer than `pub entry: ArenaId<Block>`
5. **No PhantomData**: No need for phantom type parameters
6. **Easier rkyv Support**: Each type has its own rkyv implementation
7. **Zero Cost**: Still `#[repr(transparent)]` with no runtime overhead
8. **Better Tooling**: IDE autocomplete and docs are cleaner with concrete types

### Comparison with Generic Approach

| Aspect | Specialized (`BlockId`) | Generic (`ArenaId<Block>`) |
|--------|------------------------|----------------------------|
| Type safety | ✅ Complete separation | ✅ Complete separation |
| Error messages | ✅ Clear concrete types | ⚠️ Shows generic parameters |
| Code clarity | ✅ Simple, direct | ⚠️ Requires understanding generics |
| Implementation | ⚠️ Repeat per type (or use macro) | ✅ Write once |
| rkyv support | ✅ Straightforward | ✅ Requires trait bounds |
| PhantomData | ✅ Not needed | ❌ Required |

**Decision**: Use specialized types. While it requires more code (mitigated by a macro), the benefits in type safety, clarity, and error messages outweigh the duplication.

### Why Specialized Arena Types?

1. **Maximum Type Safety**: `BlockArena` and `TBlockArena` are completely incompatible types
2. **Clearest Error Messages**: Errors show concrete types like `BlockArena` vs `Arena<Block>`
3. **Strongest Guarantees**: Cannot accidentally mix arenas or IDs of different types
4. **Simplest Mental Model**: Each IR level has its own distinct arena type
5. **Best API Clarity**: `blocks: BlockArena` is clearer than `blocks: Arena<Block>`
6. **Paired Generation**: Macro ensures arena and ID are always correctly paired
7. **Zero Generic Overhead**: No generic parameters anywhere

### Comparison of Approaches

| Aspect | Specialized Arena+ID | Generic `Arena<T>` | Generic `ArenaId<T>` |
|--------|---------------------|---------------------|---------------------|
| Type safety | ✅ Maximum | ✅ Good | ✅ Good |
| Error clarity | ✅ Best | ⚠️ Shows generics | ⚠️ Shows generics |
| API clarity | ✅ `BlockArena` | ⚠️ `Arena<Block>` | ⚠️ `Arena<Block>` |
| Cannot mix types | ✅ Compile error | ✅ Compile error | ✅ Compile error |
| Implementation | ⚠️ Macro per pair | ✅ Once | ✅ Once + ID macro |
| Generic parameters | ✅ None | ❌ Everywhere | ⚠️ On Arena |

**Decision**: Use fully specialized arena+ID pairs for maximum clarity and type safety. The macro makes duplication painless while maintaining all benefits.

### Rkyv Implementation Details

Each specialized ID type wraps a `usize` index, which is trivially serializable with rkyv:

```rust
#[cfg(feature = "rkyv-impl")]
impl rkyv::Archive for BlockId {
    type Archived = rkyv::Archived<usize>;
    type Resolver = rkyv::Resolver<usize>;
    
    #[inline]
    unsafe fn resolve(&self, pos: usize, resolver: Self::Resolver, out: *mut Self::Archived) {
        self.0.resolve(pos, resolver, out);
    }
}

#[cfg(feature = "rkyv-impl")]
impl<S: rkyv::ser::Serializer + ?Sized> rkyv::Serialize<S> for BlockId {
    #[inline]
    fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, S::Error> {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "rkyv-impl")]
impl<D: rkyv::de::Fallible + ?Sized> rkyv::Deserialize<BlockId, D> for rkyv::Archived<usize> {
    #[inline]
    fn deserialize(&self, deserializer: &mut D) -> Result<BlockId, D::Error> {
        Ok(BlockId(rkyv::Deserialize::<usize, D>::deserialize(self, deserializer)?))
    }
}
```

Benefits:
- No complex pointer management needed
- Deserialization is straightforward reconstruction
- Each type has explicit, clear rkyv implementation
- `#[cfg_attr]` derive can be used for consistency

### Type Parameter Considerations

Many types have default type parameters like:
```rust
pub enum SValue<I = Id<SValueW>, B = Id<SBlock>, F = SFunc>
```

These should be updated to:
```rust
pub enum SValue<I = SValueId, B = SBlockId, F = SFunc>
```

But keep the generic parameters for flexibility in trait implementations. This allows:
1. Testing with mock ID types
2. Future alternative representations
3. Trait implementations that work with any ID type

## Workplan

- [x] Analyze codebase structure
- [x] Identify all uses of `id-arena::Id` and `id-arena::Arena`
- [x] Document affected types and modules
- [ ] Create `define_arena!` macro in `swc-ll-common`:
  - [ ] Generates paired arena type and ID type
  - [ ] Includes `alloc()`, indexing, iteration methods
  - [ ] rkyv derive support for both types
  - [ ] `Default` implementation
  - [ ] arena-traits support
- [ ] Define specialized arena+ID pairs using macro in each crate:
  - [ ] `BlockArena` + `BlockId` in `swc-cfg`
  - [ ] `TBlockArena` + `TBlockId` in `swc-tac`
  - [ ] `SBlockArena` + `SBlockId` in `swc-ssa`
  - [ ] `SValueArena` + `SValueId` in `swc-ssa`
  - [ ] `OptBlockArena` + `OptBlockId` in `swc-opt-ssa`
  - [ ] `OptValueArena` + `OptValueId` in `swc-opt-ssa`
- [ ] Migrate `swc-cfg` (simplest, fewest dependencies):
  - [ ] Update `Func::entry: Id<Block>` → `BlockId`
  - [ ] Update `Cfg::blocks: Arena<Block>` usage
  - [ ] Update `Term`, `Catch` variants
  - [ ] Update all method signatures
- [ ] Migrate `swc-tac` (depends on swc-cfg):
  - [ ] Update `TFunc::entry: Id<TBlock>` → `TBlockId`
  - [ ] Update `TCfg::blocks: Arena<TBlock>` usage
  - [ ] Update `TPostcedent`, `TTerm`, `TCatch`
  - [ ] Update all conversions from CFG
- [ ] Migrate `swc-ssa` (depends on swc-tac and swc-cfg):
  - [ ] Update `SFunc::entry: Id<SBlock>` → `SBlockId`
  - [ ] Update `SCfg::blocks` and `SCfg::values`
  - [ ] Update `SBlock::params` and `SBlock::stmts`
  - [ ] Update `SValue`, `SPostcedent`, `STerm`, `STarget`, `SCatch`
  - [ ] Update all conversions from TAC
- [ ] Migrate `swc-opt-ssa` (depends on swc-ssa):
  - [ ] Update `OptFunc::entry: Id<OptBlock>` → `OptBlockId`
  - [ ] Update `OptCfg` arenas
  - [ ] Update `OptBlock::params`
  - [ ] Update all value and block references
- [ ] Update `swc-ll-common` trait implementations if needed
- [ ] Run full test suite after each crate migration
- [ ] Add rkyv serialization tests for specialized arena and ID types
- [ ] Update documentation with examples of new types
- [ ] Performance validation (ensure no regressions)
- [ ] Remove `id-arena` from workspace `Cargo.toml`
- [ ] Remove `arena-traits` id-arena feature if no longer needed
- [ ] Verify clean build with no id-arena references

## Alternative Approaches Considered

### 1. Fork id-arena and add rkyv support
- **Pros**: Minimal code changes
- **Cons**: Maintenance burden, less control

### 2. Use raw usize everywhere
- **Pros**: Simple, no wrapper overhead
- **Cons**: Loss of type safety, easy to mix up different arena indices

### 3. Generic ArenaId<T> wrapper
- **Pros**: Write implementation once, consistent behavior
- **Cons**: Generic parameters in error messages, requires PhantomData, less clear API

### 4. Generic wrapper trait
- **Pros**: More flexible
- **Cons**: Most complex, harder to understand

**Decision**: Use specialized newtype wrappers (`BlockId`, `TBlockId`, etc.) for maximum type safety and clarity. A macro reduces code duplication while maintaining the benefits of specialized types.

## Risks and Mitigation

1. **Risk**: Breaking changes across entire codebase
   - **Mitigation**: This is expected for 0.8.0; phased migration per crate with testing
   - **Note**: No backward compatibility required

2. **Risk**: Performance regression
   - **Mitigation**: Use `#[repr(transparent)]` and `#[inline]` everywhere; zero-cost abstraction

3. **Risk**: Arena-traits compatibility issues
   - **Mitigation**: Test with existing arena-traits usage patterns

4. **Risk**: Rkyv serialization edge cases
   - **Mitigation**: Add comprehensive serialization tests; usize is trivially serializable

5. **Risk**: Migration errors during replacement
   - **Mitigation**: Migrate one crate at a time; compiler will catch type mismatches

6. **Risk**: Arena iteration patterns may differ slightly
   - **Mitigation**: Our specialized arenas' `.iter()` returns `(CustomId, &T)` directly - even better ergonomics!

## Implementation Examples

### Macro Usage

```rust
// In swc-cfg/src/lib.rs
use swc_ll_common::define_arena;

// One macro call generates both BlockArena and BlockId
define_arena!(pub BlockArena, pub BlockId for Block);

// Results in:
// - pub struct BlockArena { items: Vec<Block> }
// - pub struct BlockId(usize)
// - All necessary trait implementations
```

### Generated Types

The macro expands to create fully specialized types:

```rust
// Generated BlockArena type
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
pub struct BlockArena {
    items: Vec<Block>,
}

impl BlockArena {
    pub fn new() -> Self { ... }
    pub fn alloc(&mut self, value: Block) -> BlockId { ... }
    pub fn iter(&self) -> impl Iterator<Item = (BlockId, &Block)> { ... }
    // ... more methods
}

// Generated BlockId type
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "rkyv-impl", derive(rkyv::Archive, rkyv::Serialize, rkyv::Deserialize))]
#[repr(transparent)]
pub struct BlockId(usize);

impl BlockId {
    pub fn new(index: usize) -> Self { Self(index) }
    pub fn index(self) -> usize { self.0 }
}

// Indexing
impl std::ops::Index<BlockId> for BlockArena {
    type Output = Block;
    fn index(&self, id: BlockId) -> &Self::Output { &self.items[id.0] }
}

// arena-traits support
impl arena_traits::IndexAlloc<Block> for BlockArena {
    type Id = BlockId;
    fn alloc(&mut self, value: Block) -> BlockId { ... }
}
```

### Usage Pattern

```rust
// Create a CFG with specialized arena
let mut cfg = Cfg {
    blocks: BlockArena::new(),  // Not Arena<Block>
    // ...
};

// Allocate a block - returns BlockId (not Id<Block>)
let block_id: BlockId = cfg.blocks.alloc(Block::default());

// Index into arena with BlockId
let block_ref: &Block = &cfg.blocks[block_id];

// Iterate - gets (BlockId, &Block) pairs
for (block_id, block) in cfg.blocks.iter() {
    // block_id is already BlockId type
    // ...
}

// Type safety: cannot mix different arena types
let mut ssa_cfg = SCfg {
    blocks: SBlockArena::new(),  // Different type!
    values: SValueArena::new(),  // Also different!
    // ...
};

// This would be a compile error:
// cfg.blocks[some_sblock_id]  // ❌ SBlockId doesn't work with BlockArena
```

### Benefits in Practice

```rust
// Clear field types
pub struct Cfg {
    pub blocks: BlockArena,  // ✅ Clear: it's a BlockArena
    // not: pub blocks: Arena<Block>  // ⚠️ Generic type
}

pub struct SCfg {
    pub blocks: SBlockArena,   // ✅ Different type from BlockArena
    pub values: SValueArena,   // ✅ Also different
}

// Clear function signatures
fn process_block(arena: &BlockArena, id: BlockId) -> &Block {
    &arena[id]
}

// Impossible to accidentally mix
fn wrong(block_arena: &BlockArena, ssa_id: SBlockId) {
    // ❌ Compile error: SBlockId doesn't index into BlockArena
    let x = &block_arena[ssa_id];
}
```

## Success Criteria

- [ ] All types compile with new specialized identifier types
- [ ] Each ID type is completely distinct (cannot be mixed)
- [ ] All existing tests pass
- [ ] Rkyv serialization/deserialization works for all IR types
- [ ] Arena operations work seamlessly with new ID types
- [ ] No performance regression (all operations should inline)
- [ ] Error messages are clear and show concrete type names
- [ ] Code is maintainable and well-documented
- [ ] Migration completed incrementally per crate
- [ ] No public API exposes `id_arena` types
- [ ] `id-arena` dependency completely removed
- [ ] Clean cargo build with no warnings
- [ ] Ready for 0.8.0 breaking release
