# Cycle-two verification record

**Finite result.** Even inner product on three product pairs needs exactly seven affine clauses without a helper, six with one helper and five with two. The independent lower bound gives at most six projected conflicts from any four two-helper clauses, while the odd set requires at least seven affine flats. The five-clause witness uses the following packed pairs of rows in coordinate order $x_1,x_2,x_3,y_1,y_2,y_3,w_0,w_1$, with the right-hand side in bit zero. [Lower bound](synthesis.md) · [Construction and proof](five_points.md)

~~~text
(128,256) (130,260) (160,272) (162,284) (9,226)
~~~

Direct evaluation of all 256 lifted points found 28 visible inputs with zero witnesses, 12 with one, 22 with two, and 2 with three. Zero witnesses occurred exactly on the odd inputs. Removing one clause at a time accepted 19, 19, 19, 19 and 16 additional odd inputs, respectively. With the first helper order the general solver produced 5, 10, 15 flats in 117, 334, 631 dense bits and tested 55 graph pairs across both steps. Reversing the order gave 5, 7, 9 flats in 117, 227, 383 bits and 27 graph pairs. The input has width two and one-bit coefficients. Both orders were checked against direct projection. These are measured work counts for these runs. The five-clause result is a finite optimum and leaves the asymptotic unrestricted exponent open. [Independent replay](mixed_line.py) · [Trace](mixed_line.json) · [Parallel profile exclusion](mixed_parallel.md)

## Verification commands

All commands in the table ran from the parent research directory on 23 November 2026 with Python 3.12.14, the existing CaDiCaL 2.1.2 and Lean 4.36.0. Every process exited zero. Times are elapsed seconds from a replay with at most three checks running concurrently on a shared machine. They do not measure asymptotic complexity. Here `$AUDIT` names a writable temporary directory for outputs. The first-cycle replay additionally compared four older traces. The new replay compared the synthesis probe, six-flat histogram, mixed witness trace, and constructions output with the four saved artifacts. Both five-clause SAT probes at $k=3$ reproduced their recorded UNKNOWN within the 2,000-conflict budget. The five-clause construction was verified independently of these probes.

| Command | Seconds |
|---|---:|
| `python3 cycle2/synthesis.py --probe --output "$AUDIT/synthesis-results.json"` | 8.55 |
| `python3 cycle2/synthesis_points.py` | 1.56 |
| `python3 cycle2/five_points.py` | 0.23 |
| `python3 cycle2/mixed_line.py > "$AUDIT/mixed_line.json"` | 0.24 |
| `python3 cycle2/constructions.py > "$AUDIT/constructions-results.txt"` | 18.17 |
| `python3 cycle2/geometric.py` | 4.59 |
| `python3 cycle2/generator_flat.py` | 12.46 |
| `python3 cycle2/matching_encoding.py` | 6.86 |
| `python3 cycle2/tour_encoding.py` | 1.41 |
| `python3 cycle2/assignment_lower.py` | 5.71 |
| `python3 cycle2/order_search.py` | 2.25 |
| `python3 cycle2/weighted_checks.py` | 0.31 |
| `python3 cycle2/weighted_profile.py` | 0.19 |
| `python3 cycle2/weighted_slices.py` | 0.37 |
| `python3 cycle2/weighted_syndrome.py` | 0.41 |
| `lean cycle2/InterfaceCover.lean` | 3.24 |
| `python3 reproduce.py` | 39.89 |

## Files for review

The finite helper result uses the parent flat solver and the following cycle-two files.

- Proofs and scope are in `synthesis.md`, `five_points.md`, `mixed_parallel.md` and `mixed_line.md`.
- Replayers are `synthesis.py`, `synthesis_points.py`, `five_points.py` and `mixed_line.py`.
- Saved evidence is in `synthesis-results.json`, `synthesis-points-results.json` and `mixed_line.json`.

Other cycle-two results have separate assumptions and proofs.

- Clause geometry and cross-block restrictions use `geometric.md`, `geometric.py`, `constructions.md`, `constructions.py`, `constructions-results.txt`, `weighted.md`, `weighted_checks.py`, `weighted_profile.py`, `weighted_slices.md` and `weighted_slices.py`.
- Elimination order and circuit connections use `order_search.md`, `order_search.py`, `generator_flat.md`, `generator_flat.py`, `sources.md`, `weighted_syndrome.py` and `InterfaceCover.lean`.
- Matching and tour results use `assignment_lower.md`, `assignment_lower.py`, `matching_encoding.md`, `matching_encoding.py`, `tour_encoding.md`, `tour_encoding.py` and `tour_review.md`.

The tour lower bound uses the rectangle theorem in the cited 2026 preprint.
