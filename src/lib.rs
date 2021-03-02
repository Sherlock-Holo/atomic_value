//! this crate provides a way that you can load or store value atomically like
//! Golang `AtomicValue`.

#[cfg(not(loom))]
use std::cell::UnsafeCell;
#[cfg(not(loom))]
use std::hint::spin_loop as spin_loop_hint;
use std::mem;
#[cfg(not(loom))]
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
#[cfg(not(loom))]
use std::sync::Arc;

#[cfg(loom)]
use loom::cell::UnsafeCell;
#[cfg(loom)]
use loom::sync::atomic::{spin_loop_hint, AtomicBool};
#[cfg(loom)]
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
        while self
            .using
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            spin_loop_hint()
        }

        #[cfg(loom)]
        let value = unsafe { &*self.value.with(|pointer| pointer) }.clone();

        #[cfg(not(loom))]
        let value = unsafe { &*self.value.get() }.clone();

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
        while self
            .using
            .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            spin_loop_hint()
        }

        #[cfg(loom)]
        let pointer = unsafe { &mut *self.value.with_mut(|pointer| pointer) };

        #[cfg(not(loom))]
        let pointer = unsafe { &mut *self.value.get() };

        let old_value = mem::replace(pointer, Arc::new(new_value));

        self.using.store(false, Ordering::Release);

        old_value
    }

    /// Stores a value into the AtomicValue if the current value is the same as the `current`
    /// value.
    ///
    /// The new value won't change any loaded values.
    ///
    /// [`swap`]: AtomicValue::swap
    ///
    /// # Example
    ///
    /// ```
    /// use atomic_value::{AtomicValue, Error};
    /// use std::sync::atomic::Ordering;
    ///
    /// let value = AtomicValue::new(10);
    ///
    /// let result = value.compare_exchange(&10, 20, Ordering::AcqRel, Ordering::Acquire);
    /// assert_eq!(*result.unwrap(), 10);
    ///
    /// let result = value.compare_exchange(&10, 30, Ordering::AcqRel, Ordering::Acquire);
    /// let Error(current, new_value) = result.unwrap_err();
    ///
    /// assert_eq!(*current, 20);
    /// assert_eq!(new_value, 30);
    /// ```
    pub fn compare_exchange(
        &self,
        current: &T,
        new_value: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Arc<T>, Error<T>>
    where
        T: PartialEq,
    {
        while self
            .using
            .compare_exchange(false, true, success, failure)
            .is_err()
        {
            spin_loop_hint()
        }

        #[cfg(loom)]
        let pointer = unsafe { &mut *self.value.with_mut(|pointer| pointer) };

        #[cfg(not(loom))]
        let pointer = unsafe { &mut *self.value.get() };

        let result = if **pointer == *current {
            Ok(mem::replace(pointer, Arc::new(new_value)))
        } else {
            Err(Error(pointer.clone(), new_value))
        };

        self.using.store(false, Ordering::Release);

        result
    }
}

unsafe impl<T: Send + Sync> Sync for AtomicValue<T> {}

/// compare exchange error.
///
/// `.0` is the current value, `.1` is the new value that is wanted set.
#[derive(Debug)]
pub struct Error<T>(pub Arc<T>, pub T);

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(loom))]
    #[test]
    fn load() {
        let n = 100;

        let atomic_value = AtomicValue::new(n);

        assert_eq!(*atomic_value.load(), n)
    }

    #[cfg(loom)]
    #[test]
    fn load() {
        loom::model(|| {
            let n = 100;

            let atomic_value = AtomicValue::new(n);

            assert_eq!(*atomic_value.load(), n)
        })
    }

    #[cfg(not(loom))]
    #[test]
    fn store() {
        let n = 100;

        let atomic_value = AtomicValue::new(0);

        atomic_value.store(n);

        assert_eq!(*atomic_value.load(), n)
    }

    #[cfg(loom)]
    #[test]
    fn store() {
        loom::model(|| {
            let n = 100;

            let atomic_value = AtomicValue::new(0);

            atomic_value.store(n);

            assert_eq!(*atomic_value.load(), n)
        })
    }

    #[cfg(not(loom))]
    #[test]
    fn compare_exchange() {
        let atomic_value = AtomicValue::new(0);

        let result = atomic_value.compare_exchange(&0, 100, Ordering::AcqRel, Ordering::Acquire);
        assert_eq!(*result.unwrap(), 0);

        let result = atomic_value.compare_exchange(&0, 200, Ordering::AcqRel, Ordering::Acquire);
        let Error(current, new_value) = result.unwrap_err();

        assert_eq!(*current, 100);
        assert_eq!(new_value, 200);
    }

    #[cfg(loom)]
    #[test]
    fn compare_exchange() {
        loom::model(|| {
            let atomic_value = AtomicValue::new(0);

            let result =
                atomic_value.compare_exchange(&0, 100, Ordering::AcqRel, Ordering::Acquire);
            assert_eq!(*result.unwrap(), 0);

            let result =
                atomic_value.compare_exchange(&0, 200, Ordering::AcqRel, Ordering::Acquire);
            let Error(current, new_value) = result.unwrap_err();

            assert_eq!(*current, 100);
            assert_eq!(new_value, 200);
        })
    }
}
