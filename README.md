# `priority-set`

A fixed size priority set suitable for no_std use.

Example:

```rust
#[derive(PartialEq)]
enum Command {
    QueryServerA,
    QueryServerB,
}

fn main() {
    // Create a priority set with 10 slots
    let mut p: PrioritySet<Command, 10> = PrioritySet::new();

    // Insert two items
    p.insert(Priority(10), Command::QueryServerA);
    p.insert(Priority(20), Command::QueryServerB);
    p.insert(Priority(30), Command::QueryServerA);
    
    // We inserted a duplicate command, so its priority was updated, but no new item was added
    assert_eq!(p.len(), 2);
    
    // Pops the highest priority item, which is QueryServerA with Priority(30)
    assert_eq!(p.pop(), Some(Command::QueryServerA));
    assert_eq!(p.pop(), Some(Command::QueryServerB));
    assert_eq!(p.pop(), None);
    
}
```

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
