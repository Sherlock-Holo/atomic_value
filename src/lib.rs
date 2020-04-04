#[cfg(not(feature = "concurrent-test"))]
use std::cell::UnsafeCell;
use std::mem;
#[cfg(not(feature = "concurrent-test"))]
use std::sync::atomic::{AtomicBool, Ordering};
#[cfg(not(feature = "concurrent-test"))]
use std::sync::Arc;

#[cfg(feature = "concurrent-test")]
use loom::cell::UnsafeCell;
#[cfg(feature = "concurrent-test")]
use loom::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "concurrent-test")]
use loom::sync::Arc;

#[derive(Debug)]
pub struct AtomicValue<T> {
    using: AtomicBool,
    value: UnsafeCell<Arc<T>>,
}

impl<T> AtomicValue<T> {
    pub fn new(value: T) -> Self {
        Self {
            using: AtomicBool::new(false),
            value: UnsafeCell::new(Arc::new(value)),
        }
    }

    pub fn load(&self) -> Arc<T> {
        while self.using.compare_and_swap(false, true, Ordering::AcqRel) {}

        #[cfg(not(feature = "concurrent-test"))]
        let value = unsafe { &*self.value.get() }.clone();

        #[cfg(feature = "concurrent-test")]
        let value = unsafe { &*self.value.with(|pointer| pointer) }.clone();

        self.using.store(false, Ordering::Release);

        value
    }

    pub fn store(&self, new_value: T) {
        self.swap(new_value);
    }

    pub fn swap(&self, new_value: T) -> Arc<T> {
        while self.using.compare_and_swap(false, true, Ordering::AcqRel) {}

        #[cfg(not(feature = "concurrent-test"))]
        let pointer = unsafe { &mut *self.value.get() };

        #[cfg(feature = "concurrent-test")]
        let pointer = unsafe { &mut *self.value.with_mut(|pointer| pointer) };

        let old_value = mem::replace(pointer, Arc::new(new_value));

        self.using.store(false, Ordering::Release);

        old_value
    }

    pub fn compare_and_swap(&self, compare: &T, new_value: T) -> Arc<T>
    where
        T: PartialEq,
    {
        while self.using.compare_and_swap(false, true, Ordering::AcqRel) {}

        #[cfg(not(feature = "concurrent-test"))]
        let pointer = unsafe { &mut *self.value.get() };

        #[cfg(feature = "concurrent-test")]
        let pointer = unsafe { &mut *self.value.with_mut(|pointer| pointer) };

        let old_value = if **pointer == *compare {
            mem::replace(pointer, Arc::new(new_value))
        } else {
            pointer.clone()
        };

        self.using.store(false, Ordering::Release);

        old_value
    }
}

unsafe impl<T: Send + Sync> Sync for AtomicValue<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load() {
        let n = 100;

        let atomic_value = AtomicValue::new(n);

        assert_eq!(*atomic_value.load(), n)
    }

    #[test]
    fn store() {
        let n = 100;

        let atomic_value = AtomicValue::new(0);

        atomic_value.store(n);

        assert_eq!(*atomic_value.load(), n)
    }

    #[test]
    fn compare_and_swap() {
        let atomic_value = AtomicValue::new(0);

        assert_eq!(*atomic_value.compare_and_swap(&0, 100), 0);
        assert_eq!(*atomic_value.compare_and_swap(&0, 200), 100)
    }
}
