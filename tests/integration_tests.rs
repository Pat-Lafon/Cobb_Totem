mod common;

use common::process_example_file;

#[test]
fn test_list_len() {
    process_example_file("examples/list_len.ml")
        .expect("list_len example failed");
}

#[test]
fn test_list_sorted() {
    process_example_file("examples/list_sorted.ml")
        .expect("list_sorted example failed");
}

#[test]
fn test_list_sorted_combined() {
    process_example_file("examples/list_sorted_joined_match.ml")
        .expect("list_sorted example failed");
}

#[test]
fn test_bst() {
    process_example_file("examples/bst.ml")
        .expect("bst example failed");
}

#[test]
fn test_rbtree() {
    process_example_file("examples/rbtree.ml")
        .expect("rbtree example failed");
}

#[test]
fn test_tree_height() {
    process_example_file("examples/tree_height.ml")
        .expect("tree_height example failed");
}

#[test]
fn test_tree_complete() {
    process_example_file("examples/tree_complete.ml")
        .expect("tree_complete example failed");
}
