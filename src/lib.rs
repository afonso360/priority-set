#![cfg_attr(not(test), no_std)]
use core::mem;
use core::cmp;


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Priority(pub usize);

impl Priority {
    pub const MIN: Priority = Priority(usize::MIN);
    pub const MAX: Priority = Priority(usize::MAX);
}

impl From<usize> for Priority {
    fn from(i: usize) -> Self {
        Self(i)
    }
}

impl From<Priority> for usize {
    fn from(p: Priority) -> Self {
        p.0
    }
}

#[derive(Debug, PartialEq)]
pub struct PrioEntry<I>
    where
        I: PartialEq
{
    item: I,
    priority: Priority,
}

/// The result of a [PrioritySet::insert] operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InsertResult {
    /// The item was inserted into an empty slot.
    Inserted,
    /// The item already exists in the set, and the priority was updated.
    Updated,
    /// We replaced an existing entry with a lower priority.
    Replaced,
    /// There was no space for this item, and all other items had higher priority, so we dropped it.
    Dropped,
}


/// PrioritySet is a fixed size Priority Set.
///
/// It never allocates, instead dropping the lowest priority item when
/// inserting a new one.
#[derive(Debug)]
pub struct PrioritySet<I, const N: usize>
    where
        I: PartialEq
{
    items: [Option<PrioEntry<I>>; N],
}


impl<I, const N: usize> PrioritySet<I, N>
    where
        I: PartialEq + core::fmt::Debug
{
    /// Initializes a new empty `PrioritySet` with `N` free slots.
    pub fn new() -> Self {
        Self {
            items: array_init_none(),
        }
    }

    /// Counts the number of occupied entries in the set
    pub fn len(&self) -> usize {
        self.items
            .iter()
            .filter(|x| x.is_some())
            .count()
    }

    /// Returns `true` if all slots in the priority set are occupied
    pub fn is_full(&self) -> bool {
        self.len() == N
    }

    /// Inserts an item with priority.
    ///
    /// If the item already exists in the set, the priority is updated. The highest priority is chosen
    /// between the existing priority and the new priority.
    ///
    /// If the set is full the least prioritary item is dropped. If all items are of higher priority
    /// than the item being inserted, no change occurs.
    ///
    /// Returns `true` if the item was inserted, `false` if it was dropped.
    pub fn insert(&mut self, priority: Priority, item: I) -> InsertResult {
        let new_entry = PrioEntry {
            priority,
            item,
        };

        // Check if item exists, and update its priority
        if let Some(entry) = self.entry_mut(&new_entry.item) {
            // The inserted priority was lower than the existing one, so we drop this insert
            if entry.priority > priority {
                return InsertResult::Dropped;
            }

            entry.priority = cmp::max(entry.priority, priority);
            return InsertResult::Updated;
        }

        // Try to find an open slot.
        let empty_slot = self.items
            .iter_mut()
            .find(|s| s.is_none());

        if let Some(slot) = empty_slot {
            let _ = mem::replace(slot, Some(new_entry));
            return InsertResult::Inserted;
        }

        // If we can't find a open slot, lets find the one that has the lowest priority
        // and that has a lower priority than the item being inserted.
        let replacement_slot = self.items
            .iter_mut()
            .min_by_key(|slot| slot.as_ref().unwrap().priority)
            .and_then(|slot| if slot.as_ref().unwrap().priority > priority {
                None
            } else {
                Some(slot)
            });

        if let Some(slot) = replacement_slot {
            let _ = mem::replace(slot, Some(new_entry));
            return InsertResult::Replaced;
        }

        return InsertResult::Dropped;
    }

    /// Gets the priority of a item, if it exists
    pub fn priority(&self, item: &I) -> Option<Priority> {
        self.entry(item)
            .map(|entry| entry.priority)

    }

    /// Returns an iterator over the entries
    ///
    /// Iteration order is not guaranteed.
    pub fn iter(&self) -> impl Iterator<Item = &PrioEntry<I>> {
        self.items
            .iter()
            .flatten()
    }

    /// Returns a mutable iterator over the entries
    ///
    /// Iteration order is not guaranteed.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PrioEntry<I>> {
        self.items
            .iter_mut()
            .flatten()
    }

    /// Finds an item entry
    pub fn entry(&self, item: &I) -> Option<&PrioEntry<I>> {
        self.iter().find(|e| e.item == *item)
    }

    /// Returns a mutable entry to an item
    pub fn entry_mut(&mut self, item: &I) -> Option<&mut PrioEntry<I>> {
        self.iter_mut().find(|e| e.item == *item)
    }
}

/// Initializes an array of fixed size `N` with `None`.
fn array_init_none<T, const N: usize>() -> [Option<T>; N] {
    let mut items: [Option<T>; N] = unsafe { core::mem::zeroed() };
    for slot in items.iter_mut() {
        *slot = None;
    }
    items
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let p: PrioritySet<i32, 10> = PrioritySet::new();

        assert_eq!(p.len(), 0);
        assert!(!p.is_full());
    }

    #[test]
    fn insert_increases_len() {
        let mut p: PrioritySet<i32, 10> = PrioritySet::new();

        assert_eq!(p.len(), 0);
        p.insert(Priority(10), 10);
        assert_eq!(p.len(), 1);
    }

    #[test]
    fn insert_updates_on_duplicate_items() {
        let mut p: PrioritySet<i32, 10> = PrioritySet::new();

        assert_eq!(p.insert(Priority(10), 10), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(20), 10), InsertResult::Updated);
        assert_eq!(p.len(), 1);
    }

    #[test]
    fn insert_drops_when_full_with_higher_priority_items() {
        let mut p: PrioritySet<i32, 2> = PrioritySet::new();

        assert_eq!(p.insert(Priority(10), 10), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(20), 11), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(5), 12), InsertResult::Dropped);

        assert_eq!(p.entry(&12), None);
    }

    #[test]
    fn insert_replaces_items_with_lower_priority_when_full() {
        let mut p: PrioritySet<i32, 2> = PrioritySet::new();

        assert_eq!(p.len(), 0);
        assert_eq!(p.insert(Priority(10), 10), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(20), 11), InsertResult::Inserted);

        // Replaces item 10, which only has 10 priority
        assert_eq!(p.insert(Priority(15), 12), InsertResult::Replaced);

        assert!(p.entry(&11).is_some());
        assert!(p.entry(&12).is_some());
    }


    #[test]
    fn insert_replaces_the_lowest_priority_item() {
        let mut p: PrioritySet<i32, 3> = PrioritySet::new();

        assert_eq!(p.insert(Priority(20), 10), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(10), 11), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(15), 12), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(30), 13), InsertResult::Replaced);

        assert!(p.entry(&10).is_some());
        assert!(p.entry(&11).is_none());
        assert!(p.entry(&12).is_some());
        assert!(p.entry(&13).is_some());
    }


    #[test]
    fn insert_updates_the_priority_of_an_item_if_it_already_exists() {
        let mut p: PrioritySet<i32, 3> = PrioritySet::new();

        assert_eq!(p.insert(Priority(10), 10), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(20), 10), InsertResult::Updated);
        assert_eq!(p.insert(Priority(5), 10), InsertResult::Dropped);

        assert_eq!(p.priority(&10), Some(Priority(20)));
    }

    #[test]
    fn iter_iterates_over_all_entries() {
        let mut p: PrioritySet<i32, 10> = PrioritySet::new();

        assert_eq!(p.insert(Priority(10), 10), InsertResult::Inserted);
        assert_eq!(p.insert(Priority(20), 11), InsertResult::Inserted);

        let mut values: Vec<_> = p.iter().collect();
        values.sort_by_key(|i| i.priority);

        assert_eq!(values, [
            &PrioEntry {
                priority: Priority(10),
                item: 10
            },
            &PrioEntry {
                priority: Priority(20),
                item: 11
            }
        ]);
    }
}
