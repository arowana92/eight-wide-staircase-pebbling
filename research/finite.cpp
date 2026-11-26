// Exhaustive decision procedure for S_{8,n}. All weights are integers.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <queue>
#include <vector>

using Vec = std::vector<int>;
using Table = std::vector<Vec>;

struct Search {
    int n, vertices, unit;
    Table adj, weight, suffix;
    Vec pebbles, potential, target_order;
    std::uint64_t candidates = 0;

    explicit Search(int length) : n(length), vertices(4*n),
        adj(vertices), weight(vertices, Vec(vertices)), suffix(vertices+1, Vec(vertices)),
        pebbles(vertices), potential(vertices) {
        auto row = [](int v) { return 1 + 2*(v%4) + (v/4)%2; };
        for (int u = 0; u < vertices; ++u) {
            target_order.push_back(u);
            for (int v = 0; v < vertices; ++v)
                if (std::abs(u/4-v/4) == 1 && std::abs(row(u)-row(v)) == 1)
                    adj[u].push_back(v);
        }
        std::stable_sort(target_order.begin(), target_order.end(),
            [&](int u, int v) { return adj[u].size() < adj[v].size(); });
        // For n >= 2 the graph is connected. BFS also covers narrow ends.
        int diameter = 0;
        for (int t = 0; t < vertices; ++t) {
            Vec dist(vertices, -1);
            std::queue<int> queue;
            queue.push(t);
            dist[t] = 0;
            while (!queue.empty()) {
                int u = queue.front(); queue.pop();
                for (int v : adj[u]) if (dist[v] < 0) {
                    dist[v] = dist[u]+1;
                    queue.push(v);
                }
            }
            for (int v = 0; v < vertices; ++v) {
                weight[v][t] = dist[v];
                diameter = std::max(diameter, dist[v]);
            }
        }
        unit = 1 << diameter;
        for (int v = vertices-1; v >= 0; --v)
            for (int t = 0; t < vertices; ++t) {
                weight[v][t] = unit >> weight[v][t];
                suffix[v][t] = std::max(suffix[v+1][t], weight[v][t]);
            }
    }

    bool reaches(int t, int value) {
        if (pebbles[t] > 0) return true;
        if (value < unit) return false;
        for (int u = 0; u < vertices; ++u) if (pebbles[u] >= 2) {
            for (int v : adj[u]) {
                pebbles[u] -= 2;
                ++pebbles[v];
                bool ok = reaches(t, value-2*weight[u][t]+weight[v][t]);
                --pebbles[v];
                pebbles[u] += 2;
                if (ok) return true;
            }
        }
        return false;
    }

    bool enumerate(int first, int left) {
        for (int t : target_order)
            if (potential[t] + left*suffix[first][t] < unit) return false;
        if (left == 0) {
            ++candidates;
            for (int t : target_order)
                if (!reaches(t, potential[t])) return false;
            std::cout << "witness (slash,row,count):";
            for (int v = 0; v < vertices; ++v) if (pebbles[v])
                std::cout << " (" << 1+v/4 << "," << 1+2*(v%4)+(v/4)%2
                          << "," << pebbles[v] << ")";
            std::cout << "\n";
            return true;
        }
        for (int v = first; v < vertices; ++v) {
            ++pebbles[v];
            for (int t = 0; t < vertices; ++t) potential[t] += weight[v][t];
            if (enumerate(v, left-1)) return true;
            for (int t = 0; t < vertices; ++t) potential[t] -= weight[v][t];
            --pebbles[v];
        }
        return false;
    }
};

int main(int argc, char** argv) {
    if (argc != 3) { std::cerr << "usage: finite LENGTH BUDGET\n"; return 2; }
    int n = std::atoi(argv[1]), budget = std::atoi(argv[2]);
    if (n < 2 || n > 20 || budget < 0 || budget > 64) return 2;
    Search search(n);
    bool ok = search.enumerate(0, budget);
    std::cout << "n=" << n << " budget=" << budget << " feasible=" << ok
              << " weight-feasible candidates tested=" << search.candidates << "\n";
}
