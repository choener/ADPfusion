#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>

#define MAX(a,b)      ( ((a) > (b)) ? (a) : (b) )
#define I2(n,i,j)     ((i)*n+(j))
#define I4(n,i,j,k,l) ((i)*n*n*n + (j)*n*n + (k)*n + (l))

int pseudoknot (int, char *);
int pairs (char, char);
void filluv (char name, char *inp, int *t, int *uv, int n, int i, int j);

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
  int cur, new, newL, newM, newR;
  int *t = calloc (n*n    , sizeof(int));
  int *u = calloc (n*n*n*n, sizeof(int));
  int *v = calloc (n*n*n*n, sizeof(int));
  // init
  for (i=0; i<n; i++) for (j=0; j<n; j++) {
    t[I2(n,i,j)] = 0;
    for (k=0; k<n; k++) for (l=0; l<n; l++) {
      u[I4(n,i,j,k,l)] = -999999;
      v[I4(n,i,j,k,l)] = -999999;
    }
  }

  for (i = n-1; i>=0; i--) for (j=i; j<n; j++) {
    // fill t table
    cur = 0;
    if (j>0) {  // T -> T c
      new = t[I2(n,i,j-1)];
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
    for (a=i; a<=j; a++) for (b=a+1; b<=j; b++) for (c=b+1; c<j; c++) {
      // ~~ i ~~ a ~~ b ~~ c ~~ j ~~
      if (1) { // (i<a && a<b && b<c && c<=j) {
        newL = u[I4(n,i  ,a,b+1,c)];
        newR = v[I4(n,a+1,b,c+1,j)];
        new = newL + newR;
        cur = MAX(cur,new);
//        printf ("Q %3d %c %3d %c %3d %c %3d %c %3d %c -- %4d + %4d = %4d\n", i,inp[i], a,inp[a], b,inp[b], c,inp[c], j,inp[j], newL, newR, new);
//        printf ("L %3d %3d %3d %3d %3d   %3d\n", n, i  , a, b+1, c, newL);
//        printf ("R %3d (%3d) %3d %3d %3d %3d   %3d\n", n, i, a+1, b, c+1, j, newR);
      }
    }; // n^5 pseudoknot loop
    t[i*n+j] = cur;
//    printf ("  %3d %c %3d %c %4d\n",i,inp[i],j,inp[j], t[I2(n,i,j)]);
    // fill up <U>
    filluv ('U', inp, t, u, n, i, j);
    // fill up <V>
    filluv ('V', inp, t, v, n, i, j);
  } // the n^2 loop

  cur = t[I2(n,0,n-1)];

  free (t);
  free (u);
  free (v);
  return cur;
}

void filluv (char name, char *inp, int *t, int *uv, int n, int i, int j) {
  int k, l, a, b;
  int cur, newL, newM, newR, new;
  for (k=i; k<=j; k++) for (l=k+1; l<=j; l++) {
    // u
    cur = -999999;
    // loop over inner part.
    for (a=i; a<=k; a++) {
      for (b=l; b<=j; b++) {
        if (pairs(inp[a], inp[j])) {
          newL = i<a        ?  t[I2(n,i,a-1)]     : 0;
          newM = a<k && b<j ? uv[I4(n,a+1,k,l,b)] : 0;
          newR = b+1<j      ?  t[I2(n,b+1,j-1)]   : 0;
          new = newL + newM + newR + 1;
          cur = MAX(cur,new);
//          printf ("%c %d %d (%d %d) %d %d   %d %d %d\n", name, i,a, k,l, b,j, newL, newM, newR);
        }
        else {
          cur = MAX(cur,-888888);
        }; // if pairs
      }; // for b
//        if (i==0 && k==1 && l==3 && j==4)
    }; // for a,b
//    if (name=='U') // && i==0 && k==2 && l==4 && j==7)
//    printf ("%c %3d %3d %3d %3d   -- (%d) %3d\n", name, i,k,l,j, uv[I4(n,i,k,l,j)], cur );
    uv[I4(n,i,k,l,j)] = cur;
  };
};

