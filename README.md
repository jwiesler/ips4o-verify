# Formal Specification and Verification of a Java Implementation of In-Place Super Scalar Sample Sort

This is the verified code and all proof files.

The code in [`src`](src) is based on [this](https://github.com/jwiesler/ips4o) Rust rewrite of the [original paper implementation](https://github.com/ips4o/ips4o).

The proofs are located in [`proofs`](proofs) and can be loaded using the KeY binaries in [`tools`](tools).
The [`contracts`](contracts) folder contains listing of subsets of all contracts used for filtering.
The proof statistics can be found in [`statistics`](statistics).


## Usage
You can either run the respective KeY binaries in [`tools`](tools) or take some inspiration from the [`justfile`](justfile).

Make sure to pass `-Dkey.contractOrder="<path to contract-order.txt>"` to java such that the contract order file is loaded.

## Caveats
* Overflow proofs and annotations can be found on the branch `overflow`. They have to be loaded using the second KeY binary [`key-2.11.0-o-exe.jar`](tools/key-2.11.0-o-exe.jar).
* To run proofs in [`contracts/constructors.txt`](contracts/constructors.txt) the `no_state` modifier on `BucketPointers::bucketStart` and `BucketPointers::bucketSize` has to be removed. Both methods are only `no_state` when using the final heap which has a soundness problem with constructors. There is currently no nicer way to do this in KeY automatically.
* The methods `Tree::classify`, `Tree::classify_all` as well as `Tree::build` were left out as future work.
* To run the code use the `bench` branch which has the proper fallback sorting algorithm not commented out.
* The sampling function `Functions::select_n` is left empty and should probably be implemented.
