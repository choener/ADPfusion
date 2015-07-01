#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define MAX(a,b) ( ((a) > (b)) ? (a) : (b) )

int pseudoknot (int, char *);
int pairs (char, char);

int main () {
  char p[10000];
  int n;
  int e;
  while (1==scanf ("%9999s", &p)) { // only GNU C
    n = strlen(p);
    e = pseudoknot (n, p);
    printf ("%s\n%d\n", p, e);
  };
  return 0;
}

int pairs (char l,char r) {
  if (l=='A' && r=='U') return 1;
  if (l=='C' && r=='G') return 1;
  if (l=='G' && r=='C') return 1;
  if (l=='G' && r=='U') return 1;
  if (l=='U' && r=='A') return 1;
  if (l=='U' && r=='G') return 1;
  return 0;
};

int pseudoknot (int n, char *inp) {
  int i, j, k, l, a, b, c;
  //int at;
  int cur;
  int new;
  int *t = calloc (n*n    , sizeof(int));
  int *u = calloc (n*n*n*n, sizeof(int));
  int *v = calloc (n*n*n*n, sizeof(int));

  for (i = n-1; i>=0; i--) for (j=i; j<n; j++) {
    // fill t table
    cur = -999999;
    if (j>0) {  // T -> T c
      new = t[i*n+j-1];
      cur = MAX(cur,new);
    }; 
    for (a=i+1; a<j-1; a++) {
      new = -999999;
      if (pairs (inp[a],inp[j])) {
        new = t[i*n+a-1] + t[(a+1)*n+j-1] + 1;
      }
      cur = MAX(cur,new);
    }; // n^3 loop
    for (a=i; a<j; a++) for (b=a; b<j; b++) for (c=b; c<j; c++) {
      // ~~ i ~~ a ~~ b ~~ c ~~ j ~~
      new = u[i*n^3+a*n^2+b*n+c] + v[a*n^3+b*n^2+c*n+j];
      cur = MAX(cur,new);
    }; // n^5 pseudoknot loop
    t[i*n+j] = cur;
    for (k=i; k<=j; k++) for (l=k; l<=j; l++) {
      // u
      cur = -999999;
      // nil, nil
      if (i==k && l==j)
        cur = 0;
      // loop over inner part
      for (a=i+1; a<k; a++) for (b=l; b<j; b++) {
        if (pairs(inp[a], inp[j])) {
          new = t[i*n+a-1] + u[(a+1)*n^3+k*n^2+b*n+j] + t[l*n+b] + 1;
          cur = MAX(cur,new);
        };
      };
      u[i*n^3+k*n^2+l*n+j] = cur;

      // v
      cur = -999999;
      // nil, nil
      if (i==k && l==j)
        cur = 0;
      // loop over inner part
      for (a=i+1; a<k; a++) for (b=l; b<j; b++) {
        if (pairs(inp[a], inp[j])) {
          new = t[i*n+a-1] + v[(a+1)*n^3+k*n^2+b*n+j] + t[l*n+b] + 1;
          cur = MAX(cur,new);
        };
      };
      v[i*n^3+k*n^2+l*n+j] = cur;
    } // n^6 loop for u,v
      // fill u, v tables
  } // the n^2 loop

//  for (i = 0 ; i<m; i++) for (j=0; j<n; j++) {
//    cur = 0;
//    if (i==0 && j==0) { // nil_nil
//      cur = p[i] == q[j];
//    }
//    if (i>0) { // step_loop
//      new = mat[(i-1) * m + j] -1;
//      if (cur < new) cur = new;
//    }
//    if (j>0) { // loop_step
//      new = mat[i * m + (j-1)] -1;
//      if (cur < new) cur = new;
//    }
//    if (i>0 && j>0) { // loop_loop
//      new = mat[(i-1) * m + (j-1)];
//      new += ((p[i] == q[j]) ? 1 : (-1));
//      if (cur < new) cur = new;
//    }
//    mat[i*m+j] = cur;
//  };
  free (t);
  free (u);
  free (v);
  return cur;
}

