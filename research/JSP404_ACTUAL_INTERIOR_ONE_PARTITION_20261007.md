# Actual interior-one three-class producer

Status: SCOPED_PASS. Final source passed strict trust-zero and genuine
normal target build; all three selected declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
Source: `Jsp000404/ActualInteriorOnePartition.lean`.

The new module constructs three nonempty classes from the original actual
legal configuration, original full-hull nonvertex p, original row score
one, nonzero reference, and `lam>pi/5`. This larger domain covers both
n4 LOW and n4 HIGH. The window argument only needs `H<3*lam`; the three
class and singleton statements do not need `pi-4*lam<lam/2`.

Its data contains a function

    classOf : {i : Fin s // i != p} -> Fin 3

and an actual original-point witness in each class. Class 1 is the apex.
The output proves the actual physical angular bounds:

* same class: angle at p is at most `pi-4*lam`;
* different classes: angle at p is at least `2*lam`;
* apex versus another class: angle at p is at least `3*lam`;
* two nonapex points: angle at p is at most `pi-2*lam`
  (`Data.nonapex_upper`).

The reference window, actual alternating rays, and zero/true/right
witnesses are selected internally. Inside the producer the classifier is
explicitly `true bit -> 1; false bit with x<=x_m -> 0; remaining false
bit -> 2`. The actual window bounds prove every classification branch.
The `Data` structure is an output; neither an angular array nor a
caller-supplied partition or separation proof is a public input.

`actual_partition_nonempty` constructs this data from the actual geometry.
`actualPartition` makes an internal classical choice from that proved
nonempty type, giving one fixed partition for later arguments.

`singleton_in_class_actual_gain` refers only to this internally produced
partition. If an actual target is its class's sole member, every other
original ray is in a different class and has actual angle at least
`2*lam>=lam` from the target. The existing genuine
`rowGain_pos_of_forall_angle_ge` then gives positive original deletion
gain. No abstract adjacency, cyclic-gap certificate, accepting table,
or caller-provided class function replaces the producer.

Necessary actual window/fan proofs are copied locally from the frozen
AngleGap source; stable public lift alternation is reused. The frozen
general producer and AngleGap sources are not edited.

This target formalizes necessary three-class and singleton steps. It does
not itself formalize all mixed-hull paper exclusions, the inverse or exact
singleton-gain equivalence, full F17/F18 capacity, or the original
arbitrary-N lower bound.

The LOW-only half-scale metric and nearest-neighbor results remain in
their frozen earlier modules with their original `lam>2*pi/9` premise;
the present larger domain does not extend those conclusions to HIGH.

Verification: final strict check exited 0 in 66.25 seconds with maximum
RSS 4,120,510,464 bytes. Genuine normal build exited 0 in 75.08 seconds
with maximum RSS 3,997,155,328 bytes and built the target in 9009 jobs.
Both final checks reported zero warnings in this source. The initial
strict run also exited 0 with standard axioms; its one redundant simp
argument warning was removed, and its exact source and raw output are
preserved separately. There were no failed Lean attempts.

The final source SHA-256 is
`e47fc2302bcd1129d883210552fe9af3b2daf89d9499041fa5f5f6e417abb053`.
The JSON receipt binds the final source, exact strict snapshot, original
raw outputs, initial warning snapshot, selected names, and real normal
build artifacts.
