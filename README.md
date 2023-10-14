# A Formally Verified Efficient Sorting Routine For Java

This repostiory contains a sorting routine for Java programs that
combines two important properties that a decent algorithm should have: [2]
1. The implementation is competitively efficient.
2. The implementation is correct in all possible application cases.

The first point is shown empirically by benchmarking (see Section 5 of
[2] and the [Sascha Witt's
repository](https://github.com/SaschaWitt/ips4o-java-benchmark)). The
correctness of the implementation has been formally proven using the
[deductive verification engine KeY](https://www.key-project.org) with
which Java programs can be verified against a formal specification
using the [Java Modeling Language
(JML)](https://www.cs.ucf.edu/~leavens/JML/index.shtml).

You can use the algorithm in your Java programs by declaring a
maven/gradle dependency in your project (s. below).

## In-Place Super Scalar Sample Sort

The sorting algorithm [1] implemented in this project is a Java
implementation of in-place super scalar sample sort (ips4o), an award
winning highly efficient sorting routine that was algorithmically
engineered to make use of CPU features like caching, predictive
execution or SIMD.

The [source code](src/main/java) is based on [this Rust
rewrite](https://github.com/jwiesler/ips4o) of the [original paper
implementation](https://github.com/ips4o/ips4o).

The source code comprises approximately 900 lines of code. The JML
specification that annotates the Java code (in comments) adds another
2500 lines to the sources.

## Using ips4o in your project

You can use the following [maven coordinates](todo) to use `ips4o` in your JVM projects.


```groovy
dependencies {
    implementation("org.key-project.ips4o:ips4o-verify:1.0")
}
```

```xml
<dependency>
    <groupId>org.key-project.ips4o</groupId>
    <artifactId>ips4o-verify</artifactId>
    <version>1.0</version>
</dependency>
```

## Verified Properties

In this case study, the following properties of the Java ips4o implementation
have been specified and successfully verified:
1. **Sorting Property:** The array is sorted after the method invocation.
2. **Permutation Property:** The content of the input array after sorting is a permutation of the initial content.
3. **Exception Safety:** No uncaught exceptions are thrown.
4. **Memory Safety:** The implementation does not modify any previously allocated memory location except the entries of the input array.
5. **Termination:** Every method invocation terminates.
6. **Absence of Overflows:** During the execution of the method, no integer operation will overflow or underflow.

The top-level specification of the sorting routine reads as follows:
```
/*@ public normal_behaviour
  @ requires values.length <= Buffers.MAX_LEN;
  @
  @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
  @ ensures Functions.isSortedSlice(values, 0, values.length);
  @
  @ assignable values[*];
  @*/
public static void sort(int[] values) { ... }
```

This repository contains the verified code incl. the specification and all proof files.

## Usage

### Compilation

In order to compile the sources invoke
```
./gradlew compileJava
```

In order to obtain a jar file with the binary class files of the implementation invoke
```
./gradlew jar
```
and find the jar file in `./build/libs/ips4o-verify-1.0.jar`.

### Verification

In order to check / redo the proofs, you can load the interactive interface of KeY using
```
make run
```

To check whether all proofs can be replpayed, invoke
```
make check
```
This may take some time (possible hours).

You find the respective KeY binaries in the directory
[`tools`](tools). The [`Makefile`](Makefile) gives you hints on how to
execute the checker.

The proofs are located in [`proofs`](proofs) and can be loaded using
the KeY binaries in [`tools`](tools).

The [`contracts`](contracts) folder contains listing of subsets of all
contracts used for filtering.  The proof statistics can be found in
[`statistics`](statistics).


Make sure to pass `-Dkey.contractOrder="<path to contract-order.txt>"`
to java such that the contract order file is loaded.

## Caveats

* The overflow proofs have been conducted after the other proofs. The
  annotated sources can be found under
  [`src/main/java-overflow`](src/main/java-overflow). In them most
  artifacts are assumed without proving them (using the `_free`) since
  they have been shown in the original proof obligations.  They have
  to be loaded using the second KeY binary
  [`key-2.11.0-o-exe.jar`](tools/key-2.11.0-o-exe.jar).

* To run proofs in
  [`contracts/constructors.txt`](contracts/constructors.txt) the
  `no_state` modifier on `BucketPointers::bucketStart` and
  `BucketPointers::bucketSize` has to be removed. Both methods are
  only `no_state` when using the final heap which has a soundness
  problem with constructors. There is currently no nicer way to do
  this in KeY automatically. The Makefile takes care of this
  adaptation.

* The methods `Tree::classify`, `Tree::classify_all` as well as `Tree::build` were left out as future work.

* To run the code use the `bench` branch which has the proper fallback sorting algorithm not commented out.

* The sampling function `Functions::select_n` is left empty and should probably be implemented.

## Publications

1. Axtmann, M., Ferizovic, D., Sanders, P., Witt, S.: [*Engineering
in-place (shared- memory) sorting
algorithms*](https://dl.acm.org/doi/full/10.1145/3505286). ACM
Transaction on Parallel Computing 9(1), 2:1– 2:62 (2022), see also
[github.com/ips4o](https://github.com/ips4o). Conference version in
ESA 2017

2. B. Beckert, P. Sanders, M. Ulbrich, J. Wiesler, and S. Witt:
   *Formally Verifying an Efficient Sorter*. arxiv
