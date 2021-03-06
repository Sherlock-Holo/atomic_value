#[cfg(loom)]
use loom::sync::Arc;
#[cfg(loom)]
use loom::thread;

#[cfg(loom)]
use atomic_value::AtomicValue;

#[cfg(loom)]
#[test]
fn concurrent_store() {
    loom::model(|| {
        let atomic_value = Arc::new(AtomicValue::new(1));

        let threads = (0..2)
            .map(|_| {
                let atomic_value = atomic_value.clone();

                thread::spawn(move || {
                    let value = atomic_value.load();
                    atomic_value.store(*value + 1);
                })
            })
            .collect::<Vec<_>>();

        for th in threads {
            th.join().unwrap();
        }
    })
}
