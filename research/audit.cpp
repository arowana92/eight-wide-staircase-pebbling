// Independent C++17 audit of the five-fourths certificate. Input: L, slash
// totals, R on each line. No potential file or solver library is used.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using Vec = std::vector<int>;
using Mask = std::uint64_t;
struct Rule { int left, right; Vec word; };

std::vector<Rule> read_rules(const char* file) {
    std::ifstream input(file);
    if (!input) throw std::runtime_error("cannot read rules");
    std::vector<Rule> rules;
    std::string line;
    while (std::getline(input,line)) {
        std::istringstream stream(line);
        Vec entries;
        int z;
        while (stream >> z) entries.push_back(z);
        if (!stream.eof() || entries.size() < 3 || entries.size() > 15 ||
            *std::min_element(entries.begin(),entries.end()) < 0 ||
            std::accumulate(entries.begin(),entries.end(),0) > 25)
            throw std::runtime_error("unsupported certificate line");
        rules.push_back({entries.front(),entries.back(),Vec(entries.begin()+1,entries.end()-1)});
    }
    if (rules.empty()) throw std::runtime_error("empty certificate");
    return rules;
}

class PhysicalWindow {
    int n, physical, size;
    std::vector<Vec> adj, slash;
    Vec stock;
    std::vector<std::vector<Mask>> weight;
    Mask scale, all;

    Mask neighbors(Mask sites) const {
        Mask result = 0;
        while (sites) {
            int u = __builtin_ctzll(sites);
            sites &= sites-1;
            for (int v : adj[u]) result |= Mask(1)<<v;
        }
        return result;
    }

    bool solvable() const {
        std::vector<Mask> value(size,0);
        Mask reached = 0;
        Vec sources, counts, stride;
        int subsets = 1;
        for (int u = 0; u < size; ++u) if (stock[u]) {
            for (int v = 0; v < size; ++v) value[v] += stock[u]*weight[u][v];
            reached |= Mask(1)<<u;
            sources.push_back(u); counts.push_back(stock[u]); stride.push_back(subsets);
            subsets *= stock[u]+1;
        }
        if ((reached & all) == all) return true;
        for (int t = 0; t < physical; ++t) if (!stock[t]) {
            if (value[t] < scale) return false;
            bool has_sender = false;
            for (int u : adj[t]) has_sender |= value[u] >= 2*scale;
            if (!has_sender) return false;
        }

        // A code is a submultiset of the stock in mixed radix. roots[code]
        // consists of possible roots of binary ancestry trees using exactly
        // those leaves. All splits use disjoint original tokens.
        std::vector<Mask> roots(subsets,0);
        for (std::size_t i = 0; i < sources.size(); ++i)
            roots[stride[i]] = Mask(1)<<sources[i];
        Vec digits(sources.size()), part_digits(sources.size());
        for (int code = 1; code < subsets; ++code) {
            if (roots[code]) continue;  // a singleton
            for (std::size_t i = 0; i < sources.size(); ++i)
                digits[i] = (code/stride[i])%(counts[i]+1);
            std::fill(part_digits.begin(),part_digits.end(),0);
            Mask merge_sites = 0;
            int part = 0;
            while (true) {
                // Advance to the next submultiset in increasing code order.
                std::size_t i = 0;
                for (; i < digits.size() && part_digits[i] == digits[i]; ++i) {
                    part -= part_digits[i]*stride[i];
                    part_digits[i] = 0;
                }
                if (i == digits.size()) break;
                ++part_digits[i]; part += stride[i];
                if (2*part > code) break;
                merge_sites |= roots[part] & roots[code-part];
            }
            roots[code] = neighbors(merge_sites);
            reached |= roots[code];
            if ((reached & all) == all) return true;
        }
        return false;
    }

    void place(const Rule& rule, int s, int remaining, int first, std::uint64_t& tested) {
        if (s == n) {
            ++tested;
            if (solvable()) throw std::runtime_error("a forbidden window is solvable");
            return;
        }
        if (!remaining) {
            place(rule,s+1,s+1 == n ? 0 : rule.word[s+1],0,tested);
            return;
        }
        for (int j = first; j < 4; ++j) {
            int u = slash[s][j];
            ++stock[u];
            place(rule,s,remaining-1,j,tested);
            --stock[u];
        }
    }

public:
    explicit PhysicalWindow(int length) : n(length),physical(4*n),size(physical+2),
        adj(size),slash(n),stock(size),weight(size,std::vector<Mask>(size,0)) {
        std::vector<std::pair<int,int>> vertices;
        for (int x = 0; x <= n+8; ++x) for (int y = -n; y <= 8; ++y) {
            if (x-y < 1 || x-y > n || x+y < 1 || x+y > 8) continue;
            slash[x-y-1].push_back(static_cast<int>(vertices.size()));
            vertices.push_back({x,y});
        }
        if (int(vertices.size()) != physical) throw std::runtime_error("bad vertex count");
        auto join = [&](int u,int v) { adj[u].push_back(v); adj[v].push_back(u); };
        for (int u = 0; u < physical; ++u) {
            auto [x,y] = vertices[u];
            for (int v = 0; v < u; ++v) {
                auto [a,b] = vertices[v];
                if (std::abs(x-a)+std::abs(y-b) == 1) join(u,v);
            }
            if (x-y == 1) join(u,physical);
            if (x-y == n) join(u,physical+1);
        }
        all = (Mask(1)<<physical)-1;
        // Obtain the common dyadic scale from the graph distances.
        std::vector<Vec> distance(size,Vec(size,-1));
        int diameter = 0;
        for (int u = 0; u < size; ++u) {
            Vec queue{u}; distance[u][u] = 0;
            for (std::size_t i = 0; i < queue.size(); ++i) for (int v : adj[queue[i]]) {
                if (distance[u][v] >= 0) continue;
                distance[u][v] = 1+distance[u][queue[i]];
                diameter = std::max(diameter,distance[u][v]); queue.push_back(v);
            }
            if (int(queue.size()) != size) throw std::runtime_error("disconnected window");
        }
        scale = Mask(1)<<diameter;
        for (int u = 0; u < size; ++u) for (int v = 0; v < size; ++v)
            weight[u][v] = scale >> distance[u][v];
        // Every site is within n steps of the left hub.
        stock[physical] = 1<<n;
        if (n <= 7 && !solvable()) throw std::runtime_error("failed positive hub control");
        stock[physical] = 0;
    }

    std::uint64_t exclude(const Rule& rule) {
        stock[physical] = rule.left; stock[physical+1] = rule.right;
        std::uint64_t tested = 0;
        place(rule,0,rule.word.front(),0,tested);
        return tested;
    }
};

void verify_windows(const std::vector<Rule>& rules) {
    std::map<int,PhysicalWindow> boards;
    std::uint64_t count = 0;
    for (const Rule& rule : rules) {
        int n = int(rule.word.size());
        auto it = boards.try_emplace(n,n).first;
        count += it->second.exclude(rule);
    }
    std::cout << "ancestry trees excluded " << count << " placements for "
              << rules.size() << " windows" << std::endl;
}

// The second transfer graph stores distinct remaining suffixes with their
// right-bank thresholds. Prefixes from different rules may coalesce.
struct Suffix { int first, tail, right; };
struct Step { int memory, right_limit; };
class SuffixMachine {
    int max_left = 0, max_letter = 0;
    std::vector<Suffix> suffix;
    std::vector<Vec> starts, memories;
    std::map<Vec,int> memory_id;
    std::map<std::tuple<int,int,int>,Step> cache;

    int intern(Vec v) {
        std::sort(v.begin(),v.end());
        v.erase(std::unique(v.begin(),v.end()),v.end());
        auto [it,fresh] = memory_id.emplace(v,int(memories.size()));
        if (fresh) memories.push_back(std::move(v));
        return it->second;
    }

public:
    explicit SuffixMachine(const std::vector<Rule>& rules) {
        for (const auto& rule : rules) max_left = std::max(max_left,rule.left);
        starts.resize(max_left+2);
        std::map<std::pair<Vec,int>,int> id;
        for (const auto& rule : rules) {
            int tail = -1;
            for (auto j = rule.word.end(); j != rule.word.begin();) {
                --j;
                max_letter = std::max(max_letter,*j);
                auto key = std::make_pair(Vec(j,rule.word.end()),rule.right);
                auto [it,fresh] = id.emplace(key,int(suffix.size()));
                if (fresh) suffix.push_back({*j,tail,rule.right});
                tail = it->second;
            }
            for (int L = 0; L <= rule.left; ++L) starts[L].push_back(tail);
        }
        intern({});
    }

    Step advance(int mem, int left, int p) {
        if (p > max_letter) return {0,-1};
        left = std::min(left,max_left+1);
        auto key = std::make_tuple(mem,left,p);
        auto hit = cache.find(key);
        if (hit != cache.end()) return hit->second;
        Vec after;
        int bound = -1;
        for (const Vec* candidates : {&memories[mem],&starts[left]}) {
            for (int i : *candidates) {
                const auto& s = suffix[i];
                if (p > s.first) continue;
                if (s.tail < 0) bound = std::max(bound,s.right);
                else after.push_back(s.tail);
            }
        }
        Step result{intern(std::move(after)),bound};
        cache.emplace(key,result);
        return result;
    }
};

struct Edge { int from,to,cost; };
void verify_transfers(const std::vector<Rule>& rules) {
    constexpr int box = 36;
    SuffixMachine machine(rules);
    using State = std::tuple<int,int,int>;
    std::map<State,int> index;
    std::vector<State> states;
    auto intern = [&](int L,int R,int memory) {
        State key{L,R,memory};
        auto [it,fresh] = index.emplace(key,int(states.size()));
        if (fresh) states.push_back(key);
        return it->second;
    };
    for (int R = box; R >= 0; --R) for (int L = 0; L <= box; ++L) intern(L,R,0);
    std::vector<Edge> edges;
    for (std::size_t i = 0; i < states.size(); ++i) {
        auto [L,R,mem] = states[i];
        for (int r = box; r >= 0; --r) {
            int p = R-r/2;
            if (p < 0) continue;
            int l = p+L/2;
            if (l > box) continue;
            Step next = machine.advance(mem,L,p);
            if (r <= next.right_limit) continue;
            int j = intern(l,r,next.memory);
            int cost = 16*p-20-4*((l-r)-(L-R));
            edges.push_back({int(i),j,cost});
        }
    }
    // Synchronous relaxation computes the minimum cost of a walk of at most
    // k edges from any state. A stationary vector is a dual certificate.
    Vec d(states.size(),0);
    for (std::size_t k = 0; ; ++k) {
        Vec next = d;
        for (auto e : edges) next[e.to] = std::min(next[e.to],d[e.from]+e.cost);
        if (next == d) break;
        if (k >= states.size()) throw std::runtime_error("negative cycle");
        d.swap(next);
    }
    for (auto e : edges) if (e.cost < d[e.to]-d[e.from])
        throw std::runtime_error("invalid recomputed potential");
    int low = *std::min_element(d.begin(),d.end());
    int high = *std::max_element(d.begin(),d.end());
    if (high != 0 || low < -56 || 4*((box+2)/2)-20 < high-low)
        throw std::runtime_error("unbounded-interface estimate failed");
    std::cout << "suffix graph: " << states.size() << " states, " << edges.size()
              << " edges, recomputed range " << low << ".." << high << "\n";
}

int main(int argc, char** argv) {
    try {
        if (argc < 2 || argc > 3) throw std::runtime_error("usage: audit RULES [windows|dual]");
        auto rules = read_rules(argv[1]);
        std::string which = argc == 3 ? argv[2] : "all";
        if (which != "all" && which != "windows" && which != "dual")
            throw std::runtime_error("unknown audit part");
        if (which != "dual") verify_windows(rules);
        if (which != "windows") verify_transfers(rules);
    } catch (const std::exception& e) {
        std::cerr << e.what() << "\n";
        return 1;
    }
}
