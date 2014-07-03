// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

Task local data management

Allows storing arbitrary types inside task-local-data (TLD), to be accessed
anywhere within a task, keyed by a global pointer parameterized over the type of
the TLD slot. Useful for dynamic variables, singletons, and interfacing with
foreign code with bad callback interfaces.

To declare a new key for storing local data of a particular type, use the
`local_data_key!` macro. This macro will expand to a `static` item appropriately
named and annotated. This name is then passed to the functions in this module to
modify/read the slot specified by the key.

```rust
local_data_key!(key_int: int)
local_data_key!(key_vector: Vec<int>)

key_int.replace(Some(3));
assert_eq!(*key_int.get().unwrap(), 3);

key_vector.replace(Some(vec![4]));
assert_eq!(*key_vector.get().unwrap(), vec![4]);
```

*/

// Casting 'Arcane Sight' reveals an overwhelming aura of Transmutation
// magic.

use core::prelude::*;

use alloc::rc::Rc;
use collections::treemap::TreeMap;
use collections::{Map, MutableMap};
use core::mem;
use core::ptr;
use core::fmt;

use local::Local;
use task::{Task, LocalStorage};

/**
 * Indexes a task-local data slot. This pointer is used for comparison to
 * differentiate keys from one another. The actual type `T` is not used anywhere
 * as a member of this type, except that it is parameterized with it to define
 * the type of each key's value.
 *
 * The value of each Key is of the singleton enum KeyValue. These also have the
 * same name as `Key` and their purpose is to take up space in the programs data
 * sections to ensure that each value of the `Key` type points to a unique
 * location.
 */
pub type Key<T> = &'static KeyValue<T>;

#[allow(missing_doc)]
pub enum KeyValue<T> { Key }

trait LocalData {}
impl<T: 'static> LocalData for T {}

// The task-local-map stores all TLD information for the currently running task.
// It is stored as an owned pointer into the runtime, and it's only allocated
// when TLD is used for the first time.
//
// The previous version of TLD handed out loans to its contained data. This
// meant that a value could not be replaced if it was currently borrowed.
// However, because all values need to be boxed anyway, this version of TLD
// just uses Rc directly, allowing for replacing values while they're borrowed.
// Because every borrow is just an Rc instead of maintaining a pointer into the
// slot, there's no worries about reallocating the map when inserting new
// values.
//
// A very common usage pattern for TLD is to use replace(None) to extract a
// value from TLD, work with it, and then store it (or a derived/new value)
// back with replace(v). Typically when this happens, there are no extant loans
// of the TLD data, which means the Rc we use is uniquely owned. In that event,
// we want to avoid any unnecessary allocation.
//
// When a value is removed from the map, the TLDValue is left behind with the
// pointer nilled out. This is because a common pattern is to use replace() to
// extract a value from TLD temporarily, only to restore it (or a new derived
// value) later. We want to avoid unnecessary shuffling of the tree for these
// temporary removals. This makes the assumption that every key inserted into a
// given task's TLD is going to be present for a majority of the rest of the
// task's lifetime, but that's a fairly safe assumption, and there's very
// little downside as long as it holds true for most keys.
//
// The Map type must be public in order to allow rustrt to see it.
#[doc(hidden)]
pub type Map = TreeMap<uint, TLDValue>;
#[unsafe_no_drop_flag]
struct TLDValue {
    // rc_ptr is transmuted from Rc<Option<T>>, possibly null
    rc_ptr: *const (),
    // drop_fn is the function that knows how to drop the rc_ptr
    drop_fn: fn(p: *const ())
}

// Gets the map from the runtime. Lazily initialises if not done so already.
unsafe fn get_local_map() -> Option<&mut Map> {
    if !Local::exists(None::<Task>) { return None }

    let task: *mut Task = Local::unsafe_borrow();
    match &mut (*task).storage {
        // If the at_exit function is already set, then we just need to take
        // a loan out on the TLD map stored inside
        &LocalStorage(Some(ref mut map_ptr)) => {
            return Some(map_ptr);
        }
        // If this is the first time we've accessed TLD, perform similar
        // actions to the oldsched way of doing things.
        &LocalStorage(ref mut slot) => {
            *slot = Some(TreeMap::new());
            match *slot {
                Some(ref mut map_ptr) => { return Some(map_ptr) }
                None => fail!("unreachable code"),
            }
        }
    }
}

/// An immutable reference to a task-local value.
///
/// The task-local data can be accessed through this value. If the task-local
/// data is replaced, this reference will still remain valid and the data will
/// be dropped when the reference goes out of scope.
// This Ref is a wrapper for an Rc. We don't use the Rc directly because we
// need an Rc<Option<T>> but the user should only ever see a Ref<T>. We could
// try to vend an Rc<T> directly by dropping the Option, but that requires us
// to play some unsafe games with the Rc value in order to preserve the ability
// to avoid allocation in the common replace(None) + replace(oldval) pattern.
// We avoid allocation there by "emptying out" the Rc, which right now means
// replacing the contained Option with a None. If we vended an Rc<T> directly
// we'd have to instead hold onto Rc<T> values where the contained T has been
// moved out, using unsafe code, and keeping extra state around in TLDValue to
// indicate that the Rc is "empty". That's all doable, but the real dirty part
// is when deallocating the map, we need to be able to destruct the Rc<T>, even
// if it's empty. We can theoretically do this by using something like
// `mem::forget(rc.try_unwrap().unwrap())`, because we should be able to rely on
// the Rc being uniquely-owned. But it still just seems like a bad idea.
#[deriving(PartialEq,Eq,PartialOrd,Ord)]
pub struct Ref<T> {
    // FIXME #12808: strange names to try to avoid interfering with
    // field accesses of the contained type via Deref
    _inner: Rc<Option<T>>
}

fn key_to_key_value<T: 'static>(key: Key<T>) -> uint {
    key as *const _ as uint
}

impl<T: 'static> KeyValue<T> {
    /// Replaces a value in task local data.
    ///
    /// If this key is already present in TLD, then the previous value is
    /// replaced with the provided data, and then returned, unwrapped if
    /// possible.
    ///
    /// If the previous value was uniquely owned by TLD, it is unwrapped and
    /// returned as `Ok(Option<T>)`. If the previous value is still referenced
    /// by any extant `Ref` instances (derived from `get()`) then it is
    /// returned as `Err(Ref<T>)`.
    ///
    /// Any previous values still extant remain usable after this method is
    /// called, but they no longer reference a value in TLD.
    ///
    /// To restore the previous behavior of TLD, where replace() would fail
    /// if there are any extant `Ref`s, call `unwrap()` on the result.
    ///
    /// # Failure
    ///
    /// Fails if there is no local task (because the current thread is not
    /// owned by the runtime).
    ///
    /// # Example
    ///
    /// ```
    /// local_data_key!(foo: int)
    ///
    /// assert_eq!(foo.replace(Some(10)).unwrap(), None);
    /// assert_eq!(foo.replace(Some(4)).unwrap(), Some(10));
    /// assert_eq!(foo.replace(None).unwrap(), Some(4));
    ///
    /// assert_eq!(foo.replace(Some(5)).unwrap(), None);
    /// let val = foo.get();
    /// assert_eq!(foo.replace(Some(6)), Err(val));
    /// assert_eq!(foo.replace(None).unwrap(), Some(6));
    /// ```
    pub fn replace(&'static self, data: Option<T>) -> Result<Option<T>, Ref<T>> {
        let map = match unsafe { get_local_map() } {
            Some(map) => map,
            None => fail!("must have a local task to insert into TLD"),
        };
        let keyval = key_to_key_value(self);

        let data = match (map.find_mut(&keyval), &data) {
            (None, _) => data,
            (Some(ref mut slot), _) if slot.rc_ptr.is_null() => {
                // We have a slot with no Rc in it
                if data.is_some() {
                    slot.rc_ptr = unsafe { mem::transmute(Rc::new(data)) };
                }
                None
            }
            (Some(slot), _) => {
                // we have a slot with an Rc
                let mut rc: Rc<Option<T>> = unsafe { mem::transmute(slot.rc_ptr) };
                match (&*rc, &data) {
                    (&None, &None) => (),
                    _ => {
                        // dratted borrowck and its lexical scopes
                        let res = match rc.try_get_mut() {
                            Some(val_ref) => Ok(mem::replace(val_ref, data)),
                            None => Err(data)
                        };
                        let data = match res {
                            Ok(oldval) => {
                                unsafe { mem::forget(rc); }
                                return Ok(oldval)
                            }
                            Err(data) => data
                        };
                        // Rc is not unique, replace it wholesale
                        if data.is_none() {
                            slot.rc_ptr = ptr::null();
                        } else {
                            slot.rc_ptr = unsafe { mem::transmute(Rc::new(data)) }
                        }
                        return Err(Ref{ _inner: rc });
                    }
                }
                unsafe { mem::forget(rc); }
                None
            }
        };
        if data.is_some() {
            let val = Rc::new(data);
            // When the task-local map is destroyed, all the data needs to be
            // cleaned up. For this reason, we create a shim function that knows how
            // to convert our *const () back into an Rc<T> so it can be dropped.
            fn d<T>(p: *const ()) {
                unsafe { mem::transmute::<_,Rc<Option<T>>>(p) };
            }
            let _new = map.insert(keyval, TLDValue {
                rc_ptr: unsafe { mem::transmute(val) },
                drop_fn: d::<T>
            });
            debug_assert!(_new, "internal bug in KeyValue.replace()");
        }
        Ok(None)
    }

    /// Borrows a value from TLD.
    ///
    /// If `None` is returned, then this key is not present in TLD. If `Some`
    /// is returned, then the returned data is a smart pointer representing a
    /// new reference to the TLD value. If `replace()` is called, the reference
    /// will continue to be valid but the referenced value will no longer be in
    /// TLD.
    ///
    /// # Example
    ///
    /// ```
    /// local_data_key!(key: int)
    ///
    /// assert!(key.get().is_none());
    ///
    /// key.replace(Some(3));
    /// assert_eq!(*key.get().unwrap(), 3);
    /// ```
    pub fn get(&'static self) -> Option<Ref<T>> {
        let map = match unsafe { get_local_map() } {
            Some(map) => map,
            None => return None,
        };
        let keyval = key_to_key_value(self);

        match map.find(&keyval) {
            Some(slot) if !slot.rc_ptr.is_null() => {
                let rc: Rc<Option<T>> = unsafe { mem::transmute(slot.rc_ptr) };
                let ret = match *rc {
                    None => None,
                    Some(_) => {
                        Some(Ref { _inner: rc.clone() })
                    }
                };
                unsafe { mem::forget(rc); }
                ret
            }
            _ => None
        }
    }

    /// Set a TLD value without returning the old value.
    ///
    /// This is a wrapper around `replace()`, for when you want to set TLD but
    /// don't care about the return value.
    pub fn set(&'static self, data: Option<T>) {
        let _ = self.replace(data);
    }
}

impl<T: 'static> Deref<T> for Ref<T> {
    #[inline(always)]
    fn deref<'a>(&'a self) -> &'a T {
        (*self._inner).as_ref().unwrap()
    }
}

impl<T: 'static + fmt::Show> fmt::Show for Ref<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}


impl Drop for TLDValue {
    fn drop(&mut self) {
        if !self.rc_ptr.is_null() {
            (self.drop_fn)(self.rc_ptr)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::prelude::*;
    use std::gc::{Gc, GC};
    use super::*;
    use std::task;

    #[test]
    fn test_tls_multitask() {
        static my_key: Key<String> = &Key;
        my_key.replace(Some("parent data".to_string()));
        task::spawn(proc() {
            // TLD shouldn't carry over.
            assert!(my_key.get().is_none());
            my_key.replace(Some("child data".to_string()));
            assert!(my_key.get().get_ref().as_slice() == "child data");
            // should be cleaned up for us
        });

        // Must work multiple times
        assert!(my_key.get().unwrap().as_slice() == "parent data");
        assert!(my_key.get().unwrap().as_slice() == "parent data");
        assert!(my_key.get().unwrap().as_slice() == "parent data");
    }

    #[test]
    fn test_tls_overwrite() {
        static my_key: Key<String> = &Key;
        my_key.replace(Some("first data".to_string()));
        my_key.replace(Some("next data".to_string())); // Shouldn't leak.
        assert!(my_key.get().unwrap().as_slice() == "next data");
    }

    #[test]
    fn test_tls_pop() {
        static my_key: Key<String> = &Key;
        my_key.replace(Some("weasel".to_string()));
        assert!(my_key.replace(None).unwrap() == "weasel".to_string());
        // Pop must remove the data from the map.
        assert!(my_key.replace(None).is_none());
    }

    #[test]
    fn test_tls_crust_automorestack_memorial_bug() {
        // This might result in a stack-canary clobber if the runtime fails to
        // set sp_limit to 0 when calling the cleanup extern - it might
        // automatically jump over to the rust stack, which causes next_c_sp
        // to get recorded as something within a rust stack segment. Then a
        // subsequent upcall (esp. for logging, think vsnprintf) would run on
        // a stack smaller than 1 MB.
        static my_key: Key<String> = &Key;
        task::spawn(proc() {
            my_key.replace(Some("hax".to_string()));
        });
    }

    #[test]
    fn test_tls_multiple_types() {
        static str_key: Key<String> = &Key;
        static box_key: Key<Gc<()>> = &Key;
        static int_key: Key<int> = &Key;
        task::spawn(proc() {
            str_key.replace(Some("string data".to_string()));
            box_key.replace(Some(box(GC) ()));
            int_key.replace(Some(42));
        });
    }

    #[test]
    fn test_tls_overwrite_multiple_types() {
        static str_key: Key<String> = &Key;
        static box_key: Key<Gc<()>> = &Key;
        static int_key: Key<int> = &Key;
        task::spawn(proc() {
            str_key.replace(Some("string data".to_string()));
            str_key.replace(Some("string data 2".to_string()));
            box_key.replace(Some(box(GC) ()));
            box_key.replace(Some(box(GC) ()));
            int_key.replace(Some(42));
            // This could cause a segfault if overwriting-destruction is done
            // with the crazy polymorphic transmute rather than the provided
            // finaliser.
            int_key.replace(Some(31337));
        });
    }

    #[test]
    #[should_fail]
    fn test_tls_cleanup_on_failure() {
        static str_key: Key<String> = &Key;
        static box_key: Key<Gc<()>> = &Key;
        static int_key: Key<int> = &Key;
        str_key.replace(Some("parent data".to_string()));
        box_key.replace(Some(box(GC) ()));
        task::spawn(proc() {
            str_key.replace(Some("string data".to_string()));
            box_key.replace(Some(box(GC) ()));
            int_key.replace(Some(42));
            fail!();
        });
        // Not quite nondeterministic.
        int_key.replace(Some(31337));
        fail!();
    }

    #[test]
    fn test_static_pointer() {
        static key: Key<&'static int> = &Key;
        static VALUE: int = 0;
        key.replace(Some(&VALUE));
    }

    #[test]
    fn test_owned() {
        static key: Key<Box<int>> = &Key;
        key.replace(Some(box 1));

        {
            let k1 = key.get().unwrap();
            let k2 = key.get().unwrap();
            let k3 = key.get().unwrap();
            assert_eq!(**k1, 1);
            assert_eq!(**k2, 1);
            assert_eq!(**k3, 1);
        }
        key.replace(Some(box 2));
        assert_eq!(**key.get().unwrap(), 2);
    }

    #[test]
    fn test_same_key_type() {
        static key1: Key<int> = &Key;
        static key2: Key<int> = &Key;
        static key3: Key<int> = &Key;
        static key4: Key<int> = &Key;
        static key5: Key<int> = &Key;
        key1.replace(Some(1));
        key2.replace(Some(2));
        key3.replace(Some(3));
        key4.replace(Some(4));
        key5.replace(Some(5));

        assert_eq!(*key1.get().unwrap(), 1);
        assert_eq!(*key2.get().unwrap(), 2);
        assert_eq!(*key3.get().unwrap(), 3);
        assert_eq!(*key4.get().unwrap(), 4);
        assert_eq!(*key5.get().unwrap(), 5);
    }

    #[test]
    #[should_fail]
    fn test_nested_get_set1() {
        static key: Key<int> = &Key;
        key.replace(Some(4));

        let _k = key.get();
        key.replace(Some(4));
    }
}
