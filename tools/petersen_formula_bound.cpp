// Exact monotone formula search for the Petersen-minus-one-vertex edge function.
// Build: c++ -std=c++20 -O3 -DNDEBUG tools/petersen_formula_bound.cpp -o /tmp/petersen-formula
// Run:   /tmp/petersen-formula                 # both second-gate operations
//        /tmp/petersen-formula or              # L-meta-2152
//        /tmp/petersen-formula and             # L-meta-2150
//
// Circuits have first signal x0 OR x4 and the stated second operation. Both
// signals may be reused freely. All remaining gates in the output cone must
// use AND/OR and have fanout at most one. This is a restricted circuit class.

#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

constexpr int vertices = 9;
constexpr int assignments = 1 << vertices;
constexpr std::array<std::pair<int, int>, 12> edges{{
    {0,1}, {1,2}, {2,3}, {3,4}, {4,0}, {0,5},
    {1,6}, {2,7}, {3,8}, {5,7}, {6,8}, {8,5}
}};

using Truth = std::bitset<assignments>;
using Permutation = std::array<int, vertices>;
using Subset = std::uint32_t;
using Start = std::chrono::steady_clock;

struct Signal {
    std::string expression;
    Truth truth;
};

struct Boundary {
    std::vector<int> positive;
    std::vector<int> negative;
};

Truth target_truth() {
    Truth target;
    for (int x = 0; x < assignments; ++x) {
        for (auto [i, j] : edges) {
            if ((x & (1 << i)) && (x & (1 << j))) {
                target.set(x);
                break;
            }
        }
    }
    return target;
}

// On the Boolean lattice, checking all immediate neighbors suffices to
// identify the minimal true and maximal false inputs of a monotone function.
Boundary boundary_of(const Truth& target) {
    Boundary result;
    for (int x = 0; x < assignments; ++x) {
        bool is_boundary = true;
        for (int v = 0; v < vertices; ++v) {
            int bit = 1 << v;
            if (target[x] && (x & bit) && target[x ^ bit]) is_boundary = false;
            if (!target[x] && !(x & bit) && !target[x ^ bit]) is_boundary = false;
        }
        if (is_boundary) (target[x] ? result.positive : result.negative).push_back(x);
    }
    return result;
}

std::vector<Signal> prefix_signals() {
    std::vector<Signal> signals;
    for (int i = 0; i < vertices; ++i) {
        Truth value;
        for (int x = 0; x < assignments; ++x) value[x] = (x & (1 << i)) != 0;
        signals.push_back({"x" + std::to_string(i), value});
    }
    signals.push_back({"(x0|x4)", signals[0].truth | signals[4].truth});
    return signals;
}

int permute_input(int mask, const Permutation& p) {
    int result = 0;
    for (int i = 0; i < vertices; ++i)
        if (mask & (1 << i)) result |= 1 << p[i];
    return result;
}

// Enumerate *all* vertex permutations preserving the edge set and first OR.
// A bijection carries the 12 edges onto themselves if it carries each into
// the edge set. The boundary inputs and primary leaves are then permuted, so
// the formula optimum is invariant. No assumed list of symmetries is needed.
std::vector<Permutation> prefix_symmetries(const Truth& target) {
    constexpr int first_mask = (1 << 0) | (1 << 4);
    Permutation p;
    std::iota(p.begin(), p.end(), 0);
    std::vector<Permutation> group;
    do {
        if (permute_input(first_mask, p) != first_mask) continue;
        bool preserves_edges = std::all_of(edges.begin(), edges.end(), [&](auto edge) {
            return target[(1 << p[edge.first]) | (1 << p[edge.second])];
        });
        if (preserves_edges) group.push_back(p);
    } while (std::next_permutation(p.begin(), p.end()));
    return group;
}

std::string orbit_key(const Truth& truth, const std::vector<Permutation>& group) {
    std::string key = truth.to_string();
    for (const auto& p : group) {
        Truth permuted;
        for (int x = 0; x < assignments; ++x) permuted[permute_input(x, p)] = truth[x];
        key = std::min(key, permuted.to_string());
    }
    return key;
}

struct Case {
    Signal second;
    int distinct_signals = 0;
    bool adds_leaf = false;
};

// After gate 1 there are ten genuine wires. Every out-of-range input index
// reads false. Commutativity leaves one empty list, eleven singleton lists
// and 66 unordered two-element lists with repetition. In particular the
// empty AND reads true and the empty OR reads false.
std::vector<Case> second_cases(bool is_or, const std::vector<Signal>& prefix,
                               const std::vector<Permutation>& group) {
    std::vector<Signal> inputs = prefix;
    inputs.push_back({"out-of-range", {}});
    std::map<std::string, Signal> functions;
    auto add = [&](Signal s) { functions.emplace(s.truth.to_string(), s); };
    add({is_or ? "OR()" : "AND()", is_or ? Truth{} : ~Truth{}});
    for (std::size_t i = 0; i < inputs.size(); ++i) {
        add(inputs[i]);
        for (std::size_t j = i; j < inputs.size(); ++j) {
            const auto& left = inputs[i];
            const auto& right = inputs[j];
            add({"(" + left.expression + (is_or ? "|" : "&") + right.expression + ")",
                 is_or ? left.truth | right.truth : left.truth & right.truth});
        }
    }

    std::map<std::string, Case> orbits;
    for (const auto& entry : functions) {
        const Signal& s = entry.second;
        // Constants do not separate a nonempty positive/negative rectangle.
        // A repeated input or the first gate supplies no extra leaf either.
        bool redundant = s.truth.none() || s.truth.all() ||
            std::any_of(prefix.begin(), prefix.end(), [&](const Signal& old) {
                return old.truth == s.truth;
            });
        std::string key = redundant ? "redundant" : orbit_key(s.truth, group);
        auto pos = orbits.emplace(key, Case{s, 0, !redundant}).first;
        ++pos->second.distinct_signals;
    }
    std::vector<Case> result;
    for (const auto& entry : orbits) result.push_back(entry.second);
    return result;
}

// common[S] records the leaves taking the prescribed side value on *every*
// assignment of subset S. The subset masks refer to positions in the list.
std::vector<Subset> common_leaves(const std::vector<int>& examples,
                                  const std::vector<Signal>& leaves, bool value) {
    std::vector<Subset> at_input;
    for (int x : examples) {
        Subset available = 0;
        for (std::size_t i = 0; i < leaves.size(); ++i)
            if (leaves[i].truth[x] == value) available |= Subset{1} << i;
        at_input.push_back(available);
    }
    std::vector<Subset> common(Subset{1} << examples.size());
    common[0] = (Subset{1} << leaves.size()) - 1;
    for (Subset s = 1; s < common.size(); ++s)
        common[s] = common[s & (s - 1)] & at_input[std::countr_zero(s)];
    return common;
}

// D[P,N] is the minimum leaves in a monotone formula true on all of P and
// false on all of N. A common separating leaf gives cost one. An OR root
// splits P: each positive is sent to a true child, while both children must
// reject all negatives. An AND root splits N in the dual way. Conversely each
// partition combines two valid child formulas. An empty part would leave a
// whole solution in the other part, so a minimum needs only nonempty splits.
// All signals are monotone: separation on the whole boundary is equivalent
// to computing the target on all 512 inputs, by upward/downward closure.
int minimum_leaves(const Boundary& boundary, const std::vector<Signal>& leaves) {
    const auto yes = common_leaves(boundary.positive, leaves, true);
    const auto no = common_leaves(boundary.negative, leaves, false);
    const std::size_t columns = no.size();
    // The DNF on the 12 two-literal edges has 24 leaves and also separates
    // every subrectangle. Byte entries therefore suffice throughout.
    const int upper = static_cast<int>(2 * edges.size());
    std::vector<std::uint8_t> cost(yes.size() * columns);
    for (Subset p = 1; p < yes.size(); ++p) {
        auto* row = cost.data() + p * columns;
        for (Subset n = 1; n < no.size(); ++n) {
            if (yes[p] & no[n]) {
                row[n] = 1;
                continue;
            }
            int best = upper;
            // To visit each unordered split once, omit the lowest set bit
            // from the enumerated half. Both submasks precede their union.
            Subset rest = p & (p - 1);
            for (Subset a = rest; a; a = (a - 1) & rest) {
                int sum = cost[a * columns + n] + cost[(p ^ a) * columns + n];
                best = std::min(best, sum);
                if (best == 2) break;
            }
            if (best != 2) {
                rest = n & (n - 1);
                for (Subset b = rest; b; b = (b - 1) & rest) {
                    best = std::min(best, int(row[b] + row[n ^ b]));
                    if (best == 2) break;
                }
            }
            row[n] = static_cast<std::uint8_t>(best);
        }
    }
    return cost.back();
}

void run(bool is_or, const Boundary& boundary, const std::vector<Signal>& prefix,
         const std::vector<Permutation>& group) {
    const auto start = Start::now();
    const std::string op = is_or ? "OR" : "AND";
    const auto cases = second_cases(is_or, prefix, group);
    int best = std::numeric_limits<int>::max();
    std::map<int, int> histogram;
    for (const auto& c : cases) {
        auto leaves = prefix;
        if (c.adds_leaf) leaves.push_back(c.second);
        int count = minimum_leaves(boundary, leaves);
        std::cout << op << " second " << (c.adds_leaf ? c.second.expression : "redundant")
                  << " | distinct truth tables " << c.distinct_signals
                  << " | formula leaves " << count << std::endl;
        histogram[count] += c.distinct_signals;
        best = std::min(best, count);
    }
    std::cout << op << " summary (" << cases.size() << " classes, including redundant):";
    for (auto [leaves, signals] : histogram)
        std::cout << ' ' << signals << " signals at " << leaves << " leaves;";
    // A binary formula with L leaves uses L-1 gates. Unary/constant gates in
    // the formula can be simplified away. The two prescribed prefix gates
    // count even when the output formula does not use both.
    std::cout << " minimum total gates = 2 + " << best << " - 1 = " << best + 1
              << " (" << std::chrono::duration<double>(Start::now() - start).count()
              << " s)" << std::endl;
}

} // namespace

int main(int argc, char** argv) {
    const std::string mode = argc == 1 ? "both" : argv[1];
    if (argc > 2 || (mode != "or" && mode != "and" && mode != "both")) {
        std::cerr << "Usage: " << argv[0] << " [or|and|both]\n";
        return 2;
    }
    const auto target = target_truth();
    const auto boundary = boundary_of(target);
    const auto prefix = prefix_signals();
    const auto group = prefix_symmetries(target);
    if (boundary.positive.size() != 12 || boundary.negative.size() != 12 || group.empty())
        throw std::logic_error("Unexpected graph boundary or symmetry group");
    std::cout << "Minimal positive inputs: " << boundary.positive.size()
              << ", maximal negative inputs: " << boundary.negative.size()
              << ", prefix-preserving automorphisms: " << group.size() << std::endl;
    if (mode != "and") run(true, boundary, prefix, group);
    if (mode != "or") run(false, boundary, prefix, group);
}
