#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>

#define MAX(a,b)      ( ((a) > (b)) ? (a) : (b) )
#define I2(n,i,j)     ((i)*n+(j))
#define I4(n,i,j,k,l) ((i)*n^3 + (j)*n^2 + (k)*n + (l))

int pseudoknot (int, char *);
int pairs (char, char);

int main () {
  char *p = calloc (10000, sizeof(char));
  int n;
  int e;
  int i;
  while (1==scanf ("%9999s", p)) { // only GNU C
    n = strlen(p);
    for (i=0;i<n;i++) {
      p[i] = toupper(p[i]);
    }
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
  int cur, new, newL, newR;
  int *t = calloc (n*n    , sizeof(int));
  int *u = calloc (n*n*n*n, sizeof(int));
  int *v = calloc (n*n*n*n, sizeof(int));
  // init
  for (i=0; i<n; i++) for (j=0; j<n; j++) {
    t[I2(n,i,j)] = -999999;
    for (k=0; k<n; k++) for (l=0; l<n; l++) {
      u[I4(n,i,j,k,l)] = -999999;
      v[I4(n,i,j,k,l)] = -999999;
    }
  }

  for (i = n-1; i>=0; i--) for (j=i; j<n; j++) {
    // fill t table
    cur = -999999;
    if (j>0) {  // T -> T c
      new = t[I2(n,i,j)];
      cur = MAX(cur,new);
    }; 
    for (a=i; a<=j; a++) {
      new = -999999;
      newL = a<=i     ? 0 : t[I2(n,i,a-1)];
      newR = a+1>=j-1 ? 0 : t[I2(n,a+1,j-1)];
      if (pairs (inp[a],inp[j])) {
        new = newL + newR + 1;
        cur = MAX(cur,new);
//        printf ("P %3d %c %3d %c -- %4d + %4d + 1\n",a, inp[a],j, inp[j], newL, newR);
      }
    }; // n^3 loop
    for (a=i; a<j; a++) for (b=a; b<j; b++) for (c=b; c<j; c++) {
      // ~~ i ~~ a ~~ b ~~ c ~~ j ~~
      new = u[i*n^3+a*n^2+b*n+c] + v[a*n^3+b*n^2+c*n+j];
      cur = MAX(cur,new);
    }; // n^5 pseudoknot loop
    t[i*n+j] = cur;
    printf ("  %3d %c %3d %c %4d\n",i,inp[i],j,inp[j], t[I2(n,i,j)]);
    //for (k=i; k<=j; k++) for (l=k; l<=j; l++) {
    //  // u
    //  cur = -999999;
    //  // nil, nil
    //  if (i==k && l==j)
    //    cur = 0;
    //  // loop over inner part
    //  for (a=i+1; a<k; a++) for (b=l; b<j; b++) {
    //    if (pairs(inp[a], inp[j])) {
    //      new = t[i*n+a-1] + u[(a+1)*n^3+k*n^2+b*n+j] + t[l*n+b] + 1;
    //      cur = MAX(cur,new);
    //    };
    //  };
    //  u[i*n^3+k*n^2+l*n+j] = cur;

    //  // v
    //  cur = -999999;
    //  // nil, nil
    //  if (i==k && l==j)
    //    cur = 0;
    //  // loop over inner part
    //  for (a=i+1; a<k; a++) for (b=l; b<j; b++) {
    //    if (pairs(inp[a], inp[j])) {
    //      new = t[i*n+a-1] + v[(a+1)*n^3+k*n^2+b*n+j] + t[l*n+b] + 1;
    //      cur = MAX(cur,new);
    //    };
    //  };
    //  v[i*n^3+k*n^2+l*n+j] = cur;
    //} // n^6 loop for u,v
  } // the n^2 loop

  cur = t[I2(n,0,n-1)];

  free (t);
  free (u);
  free (v);
  return cur;
}

