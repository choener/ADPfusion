#include <stdlib.h>
#include <stdio.h>
#include <string.h>

int needlemanWunsch (const int, const int, const char *, const char *);

int main () {
  char p[11000];
  char q[11000];
  int m;
  int n;
  int e;
  while (1==scanf ("%9999s", &p) && 1==scanf ("%9999s", &q)) { // only GNU C
    m = strlen(p);
    n = strlen(q);
    e = needlemanWunsch (m, n, p, q);
    printf ("%s\n%s\n%d\n", p, q, e);
    //free(p);
    //p=0;
  };
  return 0;
}

int needlemanWunsch (const int m, const int n, const char *p, const char *q) {
  int l = m*n;
  int i;
  int j;
  int at;
  int cur;
  int new;
  int *mat = calloc (l, sizeof(int));
  for (i = 0 ; i<m; i++) for (j=0; j<n; j++) {
    cur = -999999;
    if (i==0 && j==0) { // nil_nil
      cur = p[i] == q[j];
    }
    if (i>0) { // step_loop
      new = mat[(i-1) * m + j] -1;
      if (cur < new) cur = new;
    }
    if (j>0) { // loop_step
      new = mat[i * m + (j-1)] -1;
      if (cur < new) cur = new;
    }
    if (i>0 && j>0) { // loop_loop
      new = mat[(i-1) * m + (j-1)];
      new += ((p[i] == q[j]) ? 1 : (-2));
      if (cur < new) cur = new;
    }
    mat[i*m+j] = cur;
  };
  free (mat);
  return cur;
}

