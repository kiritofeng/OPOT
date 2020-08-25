#include "PushRelabelMinCostMaxFlow.h"

const int INF = 1<<30;
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

    PushRelabelMinCostMaxFlow <MAXNM*2, int, int> flow(0, INF, 0);

 
    for (int i = 1; i <= n; ++i) {
        flow.addEdge(0, i, 1, 0);
    }
    for (int j = 1; j <= m; ++j) {
        flow.addEdge(n + j, n+m+1, 1, 0);
    }
    for (int i = 1; i <= n; ++i) {
        for (int j = 1; j <= m; ++j) {
            flow.addEdge(i, n + j, 1, a[i][j]);
        }
    }

    auto t1 = std::chrono::high_resolution_clock::now();
 
    int ret = flow.getFlowMinCost(n+m+2, 0, n+m+1).second;

    auto t2 = std::chrono::high_resolution_clock::now();

    printf("Done!\n");

    printf("Time: %f seconds\n", std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1).count());
    printf("Optimal cost: %d\n", ret);
    return 0;
}
