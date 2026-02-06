use bumpalo::Bump;

/// Arena allocator for AST nodes
/// Provides fast batch allocation with excellent cache locality
pub struct Arena {
    bump: Bump,
}

impl Arena {
    /// Create a new arena
    pub fn new() -> Self {
        Self { bump: Bump::new() }
    }

    /// Allocate a value in the arena
    pub fn alloc<T>(&self, value: T) -> &T {
        self.bump.alloc(value)
    }

    /// Allocate a slice in the arena
    pub fn alloc_slice<T: Copy>(&self, slice: &[T]) -> &[T] {
        self.bump.alloc_slice_copy(slice)
    }
}

impl Default for Arena {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arena_allocation() {
        let arena = Arena::new();
        let x = arena.alloc(42);
        let y = arena.alloc(100);
        assert_eq!(*x, 42);
        assert_eq!(*y, 100);
    }
}
