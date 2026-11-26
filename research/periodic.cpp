// Necessary reachability tests on the doubly infinite, eight-wide strip.
// Print every surviving motif for the independent finite-window checker.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using Int = std::int64_t;
struct Site { int slash, row; };  // zero-based slash, one-based row

struct Sieve {
    int period, sites, budget;
    Int unit;
    std::vector<Site> representatives;
    std::vector<std::vector<Int>> kernel;
    std::vector<Int> weight;
    std::vector<int> pile, sender;
    Int tested = 0, survivors = 0;

    int residue(int s) const { return (s % period + period) % period; }

    int index(Site v) const {
        int s = residue(v.slash);
        int r = (v.slash - s) % 2 ? 9 - v.row : v.row;
        return 4*s + (r-1)/2;
    }

    Sieve(int p, int k) : period(p), sites(4*p), budget(k), unit(128*((1<<p)-1)),
        kernel(sites, std::vector<Int>(sites)), weight(sites), pile(sites), sender(sites) {
        for (int s = 0; s < p; ++s)
            for (int r = 1+s%2; r <= 8; r += 2)
                representatives.push_back({s,r});
        for (int t = 0; t < sites; ++t) {
            Site u = representatives[t];
            for (int ds = -7; ds <= 7; ++ds) {
                for (int r = 1; r <= 8; ++r) {
                    if ((u.slash+ds+1-r)%2) continue;
                    int distance = std::max(std::abs(ds), std::abs(r-u.row));
                    kernel[index({u.slash+ds,r})][t] += unit >> distance;
                }
            }
            // Beyond seven slashes the row no longer affects the kernel.
            for (int b = 0; b < sites; ++b) {
                for (int sign : {-1,1}) {
                    int first = 8 + residue(sign*(representatives[b].slash-u.slash)-8);
                    kernel[b][t] += Int(1) << (7+p-first);
                }
            }
        }
    }

    // Upper bound on pebbles gatherable at u without using the forbidden
    // vertices later on one branch of an acyclic move sequence.
    int ancestor(Site u, std::array<Site,8>& forbidden, int count, int depth) const {
        int b = index(u);
        if (!sender[b]) return 1;
        Int value = weight[b];
        for (int i = 0; i < count; ++i) {
            Site f = forbidden[i];
            int d = std::max(std::abs(f.slash-u.slash), std::abs(f.row-u.row));
            if (sender[index(f)]) value -= pile[index(f)]*(unit >> d);
        }
        int cap = int(value/unit);
        if (!depth || cap <= pile[b]) return cap;
        int upper = pile[b];
        forbidden[count] = u;
        for (int ds : {-1,1}) for (int dr : {-1,1}) {
            Site v{u.slash+ds,u.row+dr};
            if (v.row < 1 || v.row > 8) continue;
            bool blocked = false;
            for (int i = 0; i < count; ++i)
                if (forbidden[i].slash == v.slash && forbidden[i].row == v.row) blocked = true;
            if (!blocked) upper += ancestor(v, forbidden, count+1, depth-1)/2;
            if (upper >= cap) return cap;
        }
        return upper;
    }

    bool passes() {
        std::fill(weight.begin(), weight.end(), 0);
        std::fill(sender.begin(), sender.end(), 1);
        for (int u = 0; u < sites; ++u) if (pile[u])
            for (int t = 0; t < sites; ++t) weight[t] += pile[u]*kernel[u][t];

        bool changed;
        do {
            changed = false;
            for (int t = 0; t < sites; ++t) {
                if (!pile[t] && weight[t] < unit) return false;
                if (!sender[t] || weight[t] >= 2*unit) continue;
                sender[t] = 0;
                if (pile[t]) {
                    for (int j = 0; j < sites; ++j) weight[j] -= pile[t]*kernel[t][j];
                    changed = true;
                }
            }
        } while (changed);

        for (int depth : {1,3,6}) {
            for (int t = 0; t < sites; ++t) if (!pile[t]) {
                std::array<Site,8> forbidden;
                Site u = forbidden[0] = representatives[t];
                bool possible = false;
                for (int ds : {-1,1}) for (int dr : {-1,1}) {
                    Site v{u.slash+ds,u.row+dr};
                    if (1 <= v.row && v.row <= 8 && ancestor(v, forbidden, 1, depth-1) >= 2)
                        possible = true;
                }
                if (!possible) return false;
            }
        }
        return true;
    }

    void enumerate(int i, int left, int maximum, int anchor) {
        if (!left) {
            ++tested;
            if (passes()) {
                ++survivors;
                for (int u = 0; u < sites; ++u) if (pile[u])
                    std::cout << representatives[u].slash+1 << "," << representatives[u].row
                              << "," << pile[u] << " ";
                std::cout << "\n";
            }
            return;
        }
        if (i == sites || left > (sites-i)*maximum) return;
        if (i == anchor) {
            enumerate(i+1, left, maximum, anchor);
        } else {
            for (int q = 0; q <= std::min(left,maximum); ++q) {
                pile[i] = q;
                enumerate(i+1, left-q, maximum, anchor);
            }
            pile[i] = 0;
        }
    }

    void run() {
        // A nontrivial move needs a pile of two. A glide translation can
        // bring any maximum pile to the first slash.
        for (int m = 2; m <= budget; ++m) for (int a = 0; a < 4; ++a) {
            pile[a] = m;
            enumerate(0, budget-m, m, a);
            pile[a] = 0;
        }
        std::cerr << "period=" << period << " budget=" << budget << " anchored=" << tested
                  << " surviving=" << survivors << "\n";
    }
};

int main(int argc, char** argv) {
    if (argc < 2 || argc > 3) return 2;
    int p = std::atoi(argv[1]);
    if (p < 1 || p > 9) return 2;
    int k = argc == 3 ? std::atoi(argv[2]) : (5*p-1)/4;
    if (k < 0 || k > 16) return 2;
    Sieve(p,k).run();
}
