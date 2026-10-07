# Unique-heavy F18: a nonapex heavy is singleton

Status: **SOURCE_ONLY**. `Jsp000404/ActualF18UniqueHeavySingleton.lean` has not been compiled or kernel checked. It received independent read-only mathematical/API review. Existing PASS source files were not changed.

The original input is an actual n4 LOW minimal Model with potential 18, an original score-two center `h`, original score one for every other center, an original interior center `p`, and the actual condition that `h` is outside `p`'s internally generated canonical apex.

The two public declarations, with that same input order, are:

- `actual_unique_heavy_nonapex_angle_ge_two`: every original `j≠p,h` satisfies `angle(h,p,j)≥2λ`;
- `actual_unique_heavy_nonapex_gain`: deleting the original heavy `h` causes actual row gain at the original observer `p` of at least one.

There is no caller partition, class weight, point count, nearest-neighbor information, or desired deletion cap. No acute/nonacute hypothesis on the heavy is needed.

## Internal weighted argument

The canonical weighted partition comes from the verified original F18 ClassWeight producer. Its three original class weights are each at least four and sum to sixteen. The observer's original score one is internally known, so the heavy is a distinct original point.

Because `h` is outside the apex, every apex member is an original light point. The verified general InteriorApex consumer proves that every apex member is an original full-hull point. Its actual cross-angle condition is the full outside condition of PureLightBlock, so the apex contains at least four light points and has original weight at least eight.

The other two classes therefore have weight exactly four. In particular, the nonapex class containing `h` has weight at most four. The original heavy alone weighs four. Any other point in that class would be an original light point of weight two, giving a six-unit subset of a class whose total weight is at most four. Thus the heavy is the only original point in its actual class.

All other original rays are in different actual classes from `h`, so their physical angles from `h` at the observer are at least `2λ`. The existing actual emission theorem gives positive row gain on deleting `h`.

Heavy singletons are not forbidden by a light-target budget. They are permitted and are precisely the conclusion here; a later consumer combines actual gains at two distinct light observers with the original heavy-target deletion budget.

## Intended independent consumer

The independently owned `ActualF18UniqueHeavyAcute.lean` uses these two results to exclude two original interior centers in a unique-heavy F18 profile. Two apex memberships contradict verified apex disjointness. One apex and one nonapex membership give a triangle with actual angles at least `3λ` and `2λ`. Two nonapex memberships give two actual light-row gains, each costing two, whereas the original deletion of the heavy allows only two units of expense.

The remaining HA branch is addressed there by the actual original selected-hull turn budget. This note does not declare that consumer or the present helper kernel checked. Both need their own strict and genuine-normal verification records.
