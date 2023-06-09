#include<bits/stdc++.h>
#define ll long long
#define pii pair<int,int>
using namespace std;
const int mxn=1e4+5;
const int inf=1e8;
int main() {
   freopen("input.txt", "w", stdout);
   mt19937 rng(chrono::system_clock::now().time_since_epoch().count());

   ll n = 1e8;
   cout << n << endl;
   int q = 10000;
   cout << q << endl;

   string s = "";
   for(int i = 0; i < n; i++) cout << ((char) ('a' + rng() % 26));

   cout << endl;

   ll Limit_Insert = 100;
   ll Limit_Delete = 50; 

    for(int i = 1; i <= q; i++) {
      int t = rng() % 2;
      if(t == 0) {
         ll p = rng() % min(n + 1, Limit_Insert);
         ll sz = rng() % mxn + 1;
         string cur = "";
         for(int j = 0; j < sz; j++) cur += ((char) ('a' + rng() % 26));
         cout << "Insert "<<p<<" "<<cur<<"\n";
          n += sz;
      } else if(t == 1) {
         ll l = rng() % n + 1;
         ll r = l + rng() % min(Limit_Delete, (n - l + 1)); 
         cout << "Delete "<<l<<" "<<r<<endl;
         n -= r - l + 1;
      }
    }



   
}