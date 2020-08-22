// Push-Relabel implementation of the cost-scaling algorithm
// Runs in O( <max_flow> * log(V * max_edge_cost)) = O( V^2 E * log(V * C))
// Really fast in practice, like O(V * E), so 3e4 edges are fine.
// Operates on integers, costs are multiplied by N!!

// This version uses the look-ahead heuristic as described in
// "An efficient implementation of a scaling minimum-cost Flow algorithm"
// by A.V. Goldberg (1992)

#include <bits/stdc++.h>

using namespace std;

typedef long long ll;

template<typename flow_t = ll, typename cost_t = ll>
struct mcSFlow{
    struct Edge{
        cost_t c;
        flow_t f;
        int to, rev;
        Edge(int _to, cost_t _c, flow_t _f, int _rev):c(_c), f(_f), to(_to), rev(_rev){}
    };
    static constexpr cost_t INFCOST = numeric_limits<cost_t>::max()/2;
    cost_t eps;
    int N, S, T;
    vector<vector<Edge> > G;
    vector<unsigned int> isq, cur;
    vector<flow_t> ex;
    vector<cost_t> h;
    mcSFlow(int _N, int _S, int _T):eps(0), N(_N), S(_S), T(_T), G(_N){}
    Edge add_edge(int a, int b, cost_t cost, flow_t cap){
        assert(cap>=0);
        assert(a>=0&&a<N&&b>=0&&b<N);
        assert(a!=b);
        cost*=N;
        eps = max(eps, abs(cost));
        G[a].emplace_back(b, cost, cap, G[b].size());
        Edge ret = G[a].back();
        G[b].emplace_back(a, -cost, 0, G[a].size()-1);
        return ret;
    }
    void add_flow(Edge& e, flow_t f) {
        Edge &back = G[e.to][e.rev];
        if (!ex[e.to] && f)
        hs[h[e.to]].push_back(e.to);
        e.f -= f; ex[e.to] += f;
        back.f += f; ex[back.to] -= f;
    }
    vector<vector<int> > hs;
    vector<int> co;
    // fast max flow, lowest label version
    flow_t max_flow() {
        ex.assign(N, 0);
        h.assign(N, 0); hs.resize(2*N);
        co.assign(2*N, 0); cur.assign(N, 0);
        h[S] = N;
        ex[T] = 1;
        co[0] = N-1;
        for(auto &e:G[S]) add_flow(e, e.f);
        if(hs[0].size())
        for (int hi = 0;hi>=0;) {
            int u = hs[hi].back();
            hs[hi].pop_back();
            while (ex[u] > 0) { // discharge u
                if (cur[u] == G[u].size()) {
                    h[u] = 1e9;
                    for(unsigned int i=0;i<G[u].size();++i){
                        auto &e = G[u][i];
                        if (e.f && h[u] > h[e.to]+1){
                            h[u] = h[e.to]+1;
                            cur[u] = i;
                        }
                    }
                    if (++co[h[u]], !--co[hi] && hi < N)
                    for(int i=0;i<N;++i){
                        if (hi < h[i] && h[i] < N){
                            --co[h[i]];
                            h[i] = N + 1;
                        }
                    }
                    hi = h[u];
                } else if (G[u][cur[u]].f && h[u] == h[G[u][cur[u]].to]+1){
                    add_flow(G[u][cur[u]], min(ex[u], G[u][cur[u]].f));
                } else ++cur[u];
            }
            while (hi>=0 && hs[hi].empty()) --hi;
        }
        return -ex[S];
    }
    // begin min cost flow
    bool look_ahead(int u){
        if(ex[u]) return false;
        cost_t newHeight = h[u]-N*eps;
        for(auto const&e:G[u]){
            if(e.f == 0) continue;
            if(h[u] + e.c - h[e.to] < 0) return false; // outgoing admissible arc
            else newHeight = max(newHeight, h[e.to] - e.c); // try to make arc admissible
        }
        h[u] = newHeight - eps;
        return true;
    }
    void push(Edge &e, flow_t amt){
        if(e.f < amt) amt=e.f;
        e.f-=amt; ex[e.to]+=amt;
        G[e.to][e.rev].f+=amt; ex[G[e.to][e.rev].to]-=amt;
    }
    void relabel(int vertex){
        cost_t newHeight = -INFCOST;
        for(unsigned int i=0;i<G[vertex].size();++i){
            Edge const&e = G[vertex][i];
            if(e.f && newHeight < h[e.to]-e.c){
                newHeight = h[e.to] - e.c;
                cur[vertex] = i;
            }
        }
        h[vertex] = newHeight - eps;
    }
    static constexpr int scale=2;
    template<bool use_look_ahead = true>
    pair<flow_t, cost_t> minCostMaxFlow(){
        cost_t retCost = 0;
        for(int i=0;i<N;++i)
        for(Edge &e:G[i])
        retCost += e.c*(e.f);
        // remove this for circulation
        flow_t retFlow = max_flow();
        h.assign(N, 0); ex.assign(N, 0);
        isq.assign(N, 0); cur.assign(N,0);
        deque<int> q;
        for(;eps;eps>>=scale){
            fill(cur.begin(), cur.end(), 0);
            for(int i=0;i<N;++i)
            for(auto &e:G[i])
                if(h[i] + e.c - h[e.to] < 0 && e.f)
                    push(e, e.f);
            for(int i=0;i<N;++i){
                if(ex[i]>0){
                    q.push_back(i);
                    isq[i]=1;
                }
            }
            while(!q.empty()){
                int u=q.front();q.pop_front();
                isq[u]=0;
                while(ex[u]>0){
                    if(cur[u] == G[u].size())
                        relabel(u);
                    for(unsigned int &i=cur[u], max_i = G[u].size();i<max_i;++i){
                        Edge &e=G[u][i];
                        if(e.f == 0) continue;
                        if(h[u] + e.c - h[e.to] < 0){
                            if(use_look_ahead && look_ahead(e.to)){
                                --i;
                                continue;
                            }
                            push(e, ex[u]);
                            if(isq[e.to]==0){
                                if(q.empty() || h[e.to] < h[q.front()]) {
                                    q.push_front(e.to);
                                } else {
                                    q.push_back(e.to);
                                }
                                isq[e.to]=1;
                            }
                            if(ex[u]==0) break;
                        }
                    }
                }
            }
            if(eps>1 && eps>>scale==0){
                eps = 1<<scale;
            }
        }
        for(int i=0;i<N;++i){
            for(Edge &e:G[i]){
                retCost -= e.c*(e.f);
            }
        }
        return make_pair(retFlow, retCost/2/N);
    }
    flow_t getFlow(Edge const &e){
        return G[e.to][e.rev].f;
    }
};

const int MAXNM = 5010;

int n, m;
int temp;
int a[MAXNM][MAXNM];

int main() {
    printf("Reading input graph...");

    scanf("%d%d", &n, &m);
    for (int i = 1; i <= n; ++i) {
        scanf("%d", &temp);
    }
    for (int j = 1; j <= m; ++j) {
        scanf("%d", &temp);
    }
    for (int i = 1; i <= n; ++i) {
        for (int j = 1; j <= m; ++j) {
            scanf("%d", &a[i][j]);
        }
    }
    printf("Done!\n");

    printf("Computing minimum cost perfect matching...");

    auto t1 = std::chrono::high_resolution_clock::now();

    mcSFlow<ll, ll> flow(n+m+2, 0, n+m+1);
    for (int i = 1; i <= n; ++i) {
        flow.add_edge(0, i, 0, 1);
    }
    for (int j = 1; j <= m; ++j) {
        flow.add_edge(n + j, n+m+1, 0, 1);
    }
    for (int i = 1; i <= n; ++i) {
        for (int j = 1; j <= m; ++j) {
            flow.add_edge(i, n + j, a[i][j], 1);
        }
    }

    ll ret = flow.minCostMaxFlow().second;
    auto t2 = std::chrono::high_resolution_clock::now();

    printf("Done!\n");

    printf("Time: %f seconds\n", std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1).count());
    printf("Optimal cost: %lld\n", ret);
    return 0;
}
