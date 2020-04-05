//! this crate provides a way that you can load or store value atomically like
//! Golang `AtomicValue`.

#[cfg(not(feature = "concurrent-test"))]
use std::cell::UnsafeCell;
use std::mem;
#[cfg(not(feature = "concurrent-test"))]
use std::sync::atomic::{spin_loop_hint, AtomicBool, Ordering};
#[cfg(not(feature = "concurrent-test"))]
use std::sync::Arc;

#[cfg(feature = "concurrent-test")]
use loom::cell::UnsafeCell;
#[cfg(feature = "concurrent-test")]
use loom::sync::atomic::{spin_loop_hint, AtomicBool, Ordering};
#[cfg(feature = "concurrent-test")]
use loom::sync::Arc;

#[derive(Debug)]
/// A wrapper provides an atomic load and store of a value.
///
/// You can use [`load`] to get the current value which is wrapped by `Arc`, or use [`store`] to
/// set a new value atomically.
///
/// [`load`]: AtomicValue::load
/// [`store`]: AtomicValue::store
///
/// # Example
///
/// ```
/// use atomic_value::AtomicValue;
///
/// let value = AtomicValue::new(10);
///
/// assert_eq!(*value.load(), 10);
/// ```
pub struct AtomicValue<T> {
    using: AtomicBool,
    value: UnsafeCell<Arc<T>>,
}

impl<T> AtomicValue<T> {
    /// Create an `AtomicValue` with provide value.
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_value::AtomicValue;
    ///
    /// let value = AtomicValue::new(100);
    /// ```
    pub fn new(value: T) -> Self {
        Self {
            using: AtomicBool::new(false),
            value: UnsafeCell::new(Arc::new(value)),
        }
    }

    /// Load current value atomically.
    ///
    /// This function will return a value which wrapped by an `Arc`.
    /// After get the value, it won't be effect by [`store`], [`swap`] or [`compare_and_swap`].
    ///
    /// [`store`]: AtomicValue::store
    /// [`swap`]: AtomicValue::swap
    /// [`compare_and_swap`]: AtomicValue::compare_and_swap
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_value::AtomicValue;
    ///
    /// let value = AtomicValue::new(10);
    ///
    /// assert_eq!(*value.load(), 10);
    /// ```
    ///
    pub fn load(&self) -> Arc<T> {
        while self.using.compare_and_swap(false, true, Ordering::AcqRel) {
            spin_loop_hint()
        }

        #[cfg(not(feature = "concurrent-test"))]
        let value = unsafe { &*self.value.get() }.clone();

        #[cfg(feature = "concurrent-test")]
        let value = unsafe { &*self.value.with(|pointer| pointer) }.clone();

        self.using.store(false, Ordering::Release);

        value
    }

    /// Store a new value atomically.
    ///
    /// The new value won't change any loaded value. This method like [`swap`] but won't return
    /// old value.
    ///
    /// [`swap`]: AtomicValue::swap
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_value::AtomicValue;
    ///
    /// let value = AtomicValue::new(10);
    ///
    /// let old = value.load();
    ///
    /// assert_eq!(*old, 10);
    ///
    /// value.store(100);
    ///
    /// assert_eq!(*value.load(), 100);
    /// ```
    ///
    pub fn store(&self, new_value: T) {
        self.swap(new_value);
    }

    /// Store a new value into `AtomicValue`, and return the old value with `Arc` wrapping.
    ///
    /// The new value won't change any loaded value. This method like [`store`] but will return
    /// old value.
    ///
    /// [`store`]: AtomicValue::store
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_value::AtomicValue;
    ///
    /// let value = AtomicValue::new(10);
    ///
    /// let old = value.load();
    ///
    /// assert_eq!(*old, 10);
    ///
    /// let old = value.swap(100);
    ///
    /// assert_eq!(*old ,10);
    ///
    /// assert_eq!(*value.load(), 100);
    /// ```
    ///
    pub fn swap(&self, new_value: T) -> Arc<T> {
        while self.using.compare_and_swap(false, true, Ordering::AcqRel) {
            spin_loop_hint()
        }

        #[cfg(not(feature = "concurrent-test"))]
        let pointer = unsafe { &mut *self.value.get() };

        #[cfg(feature = "concurrent-test")]
        let pointer = unsafe { &mut *self.value.with_mut(|pointer| pointer) };

        let old_value = mem::replace(pointer, Arc::new(new_value));

        self.using.store(false, Ordering::Release);

        old_value
    }

    /// Stores a value into the AtomicValue if the current value is the same as the `current`
    /// value.
    ///
    /// The new value won't change any loaded value. This method like [`swap`], will return the
    /// old value no matter the current value is the same as the `current` value.
    ///
    /// [`swap`]: AtomicValue::swap
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_value::AtomicValue;
    ///
    /// let value = AtomicValue::new(10);
    ///
    /// assert_eq!(*value.compare_and_swap(&10, 20), 10);
    /// assert_eq!(*value.compare_and_swap(&10, 30), 20)
    /// ```
    pub fn compare_and_swap(&self, current: &T, new_value: T) -> Arc<T>
    where
        T: PartialEq,
    {
        while self.using.compare_and_swap(false, true, Ordering::AcqRel) {
            spin_loop_hint()
        }

        #[cfg(not(feature = "concurrent-test"))]
        let pointer = unsafe { &mut *self.value.get() };

        #[cfg(feature = "concurrent-test")]
        let pointer = unsafe { &mut *self.value.with_mut(|pointer| pointer) };

        let old_value = if **pointer == *current {
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
