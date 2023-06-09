/***Farhan132***/
#pragma GCC optimize("Ofast,fast-math")
#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,avx2,fma")
#pragma GCC optimization ("unroll-loops")

#include <bits/stdc++.h>
#include <cryptopp/sha.h>
#include <cryptopp/filters.h>
#include <cryptopp/base64.h>

using namespace std;
 
typedef long long ll;
typedef double dd;
typedef pair<ll , ll> ii;
typedef tuple < ll,  ll, ll > tp;
 
#define ff first
#define ss second
#define pb push_back
#define in insert
#define bug printf("**!\n")
#define mem(a , b) memset(a, b ,sizeof(a))
#define front_zero(n) __builtin_clzll(n)
#define back_zero(n) __builtin_ctzll(n)
#define total_one(n) __builtin_popcountll(n)
#define clean fflush(stdout)
 
const ll mod =  (ll) 998244353;
// const ll mod =  (ll) 1e9 + 7;
//const ll INF = numeric_limits<ll>::max()-1;
const ll INF = (ll)1e18;
 
ll dx[]={0,1,0,-1};
ll dy[]={1,0,-1,0};
ll dxx[]={0,1,0,-1,1,1,-1,-1};
ll dyy[]={1,0,-1,0,1,-1,1,-1};
 
mt19937 rng(chrono::system_clock::now().time_since_epoch().count());
 
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace __gnu_pbds;
 
template <typename T> using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

const ll N = 2e5 + 69;


ll C = 0, Mx_depth = 0;


string SHA256HashString(string aString){
    string digest;
    CryptoPP::SHA256 hash;

    CryptoPP::StringSource foo(aString, true,
    new CryptoPP::HashFilter(hash,
      new CryptoPP::Base64Encoder (
         new CryptoPP::StringSink(digest))));

    return digest;
}


struct server{

   ll n, N, SQRT, cur, counter = 0, root = 0, del = 0, cur_mx = 0, LG = 0;
   vector < ll > L, R, par, sum;
   vector < string > hash, temp, S;

   const ll unit_size = 1e6; 
   const ll Constant_Factor = 1;

   ll P1 = rng(), P2 = rng();

   string HASH(string hash1, string hash2){
      return SHA256HashString(hash1 + hash2);
   }

   string file_HASH(string c){
      return SHA256HashString(c);
   }

   ll build(ll l, ll r, ll parent = -1){
      if(l == r){
         ++cur;
         hash.push_back(file_HASH(temp[l - 1]));
         S.push_back(temp[l - 1]);
         L.push_back(-1);
         R.push_back(-1);
         sum.push_back(temp[l - 1].size());
         par.push_back(-1);
         return cur;
      }

      ll m = (l + r)/2;
      ll c1 = build(l, m);
      ll c2 = build(m + 1, r);

      ++cur;
      hash.push_back(HASH(hash[c1], hash[c2]));
      L.push_back(c1);
      R.push_back(c2);
      sum.push_back(sum[c1] + sum[c2]);
      S.push_back("");
      par.push_back(-1);
      par[c1] = par[c2] = cur;

      return cur;
   }

   string tmp = "";

   void get(ll node){
      if(L[node] == -1 && R[node] == -1){
         tmp += S[node];
         return;
      }
      if(~L[node]) get(L[node]);
      if(~R[node]) get(R[node]);
      return;
   }

   void PrintString(){
      tmp.clear();
      get(root);
      cout << tmp << endl;
      tmp.clear();
      return;
   }

   void init_build(ll _n, bool intialization = 0, string T = ""){

      if(!intialization){
         tmp.clear();
         get(root);
         swap(T, tmp);
         n += counter - del; SQRT = sqrt(N) + 1;
      }else{
         n = T.size();
         N = (n + unit_size - 1) / unit_size; SQRT = sqrt(N) + 1;
      }
      for(ll i = 0; i < T.size(); i+= unit_size){
         temp.push_back(""); ll sz = temp.size();
         for(ll j = i; j < min(n, i + unit_size); j++) temp[sz - 1] += T[j];
      }
      
      cur = 0; counter = 0; del = 0; cur_mx = 0;
      LG = log2(N) + 1;
      L.resize(1); R.resize(1); hash.resize(1);
      par.resize(1); sum.resize(1); S.resize(1);

      root = build(1, N);
      temp.resize(0);
      tmp.clear();
   }

   ii kth_element(ll node, ll k){
      if(L[node] == -1) return {node, k};
      if(sum[L[node]] < k){
         return kth_element(R[node], k - sum[L[node]]);
      }
      return kth_element(L[node], k);
   }

   void Update_ancestors(ll NODE){
      ll depth = 0;
      while(NODE != -1){
         depth++;
         if(L[NODE] + R[NODE] == -2){
            NODE = par[NODE];
            continue;
         }
         if(L[NODE] == -1 || R[NODE] == -1){
            ll c = (L[NODE] == -1 ? R[NODE] : L[NODE]);
            if(NODE == root){
               root = c;
               par[root] = -1;
               return;
            }
            ll parent = par[NODE];
            if(L[parent] == NODE) L[parent] = c;
            if(R[parent] == NODE) R[parent] = c;
            par[c] = parent;
            NODE = parent;
            continue;
         }
         hash[NODE] = HASH(hash[L[NODE]], hash[R[NODE]]);
         sum[NODE] = sum[L[NODE]] + sum[R[NODE]];
         NODE = par[NODE];
      }
      cur_mx = max(depth, cur_mx);
      Mx_depth = max(Mx_depth, depth);
      return;
   }

   void insert(ll x, string h){

      auto [NODE, pos] = kth_element(root, max(1LL, x));
      
      string T = ""; pos = pos - (x == 0);

      for(ll i = 0; i < pos; i++) T += S[NODE][i];
      T += h;
      for(ll i = pos; i < S[NODE].size(); i++) T += S[NODE][i];

      ll _N = (T.size() + unit_size - 1) / unit_size;

      for(ll i = 0; i < T.size(); i+= unit_size){
         temp.push_back(""); ll sz = temp.size();
         for(ll j = i; j < min((ll)T.size(), i + unit_size); j++) temp[sz - 1] += T[j];
      }
      N += (_N - 1);

      ll c = build(1, _N);

      R[NODE] = c;
      par[c] = NODE;

      temp.resize(0);

      // updating the ancestors
      Update_ancestors(c);

      counter += h.size();
      if(cur_mx > Constant_Factor * SQRT + 2 * LG){
         init_build(N);
         C++;
      }
   }

   void Delete(ll l, ll r){
      
      auto [N1, p1] = kth_element(root, l);
      auto [N2, p2] = kth_element(root, r);

      string h = "";
      for(ll i = 0; i < p1 - 1; i++) h += S[N1][i];
      for(ll i = p2; i < S[N2].size(); i++) h += S[N2][i];

      ll rem = (r - l + 1) + h.size();
      del += rem;
      l -= p1;

      while(rem > 0){
         auto [NODE, pos] = kth_element(root, l + 1);
         assert(pos == 1); N--;
         rem -= S[NODE].size();
         while(NODE != root){
            ll parent = par[NODE];
            if(L[parent] == NODE) L[parent] = -1;
            if(R[parent] == NODE) R[parent] = -1;
            sum[parent] -= sum[NODE];
            if(sum[parent] == 0){
               NODE = parent;
            }else{
               break;
            }
         }
         // updating the ancestors
         Update_ancestors(NODE);
      }
      if(N == 0){
         init_build((ll)h.size(), 1, h);
         return;
      }
      assert(rem == 0);
      insert(l, h);
      return;
   }

   void update(ll l, ll r, string h){
      
      Delete(l, r);
      insert(l - 1, h);
      
      return;
   }
      
   string GetBlockHash(ll blockID, string seed){
         // Server should add the string seed at the end of the mentioned block, and return the hash
      return SHA256HashString(S[blockID] + seed);
   }
   string GetNodeHash(ll NodeID){
         //server should return the hash of the node with given id
      return SHA256HashString(S[NodeID]);
   }
}Server;


struct Dynamic_Merkle_Tree{
   
   ll n, N, SQRT, cur, counter = 0, root = 0, del = 0, cur_mx = 0, LG = 0;
   vector < ll > L, R, par, sum;
   vector < string > hash, temp, S;

   const ll unit_size = 1e3; 
   const ll Constant_Factor = 2;

   ll P1 = rng(), P2 = rng();

   string HASH(string hash1, string hash2){
      return SHA256HashString(hash1 + hash2);
   }

   string file_HASH(string c){
      return SHA256HashString(c);
   }

   

   ll build(ll l, ll r, ll parent = -1){
      if(l == r){
         ++cur;
         hash.push_back(file_HASH(temp[l - 1]));
         S.push_back(temp[l - 1]);
         L.push_back(-1);
         R.push_back(-1);
         sum.push_back(temp[l - 1].size());
         par.push_back(-1);
         return cur;
      }

      ll m = (l + r)/2;
      ll c1 = build(l, m);
      ll c2 = build(m + 1, r);

      ++cur;
      hash.push_back(HASH(hash[c1], hash[c2]));
      L.push_back(c1);
      R.push_back(c2);
      sum.push_back(sum[c1] + sum[c2]);
      S.push_back("");
      par.push_back(-1);
      par[c1] = par[c2] = cur;

      return cur;
   }

   string tmp = "";

   void get(ll node){
      if(L[node] == -1 && R[node] == -1){
         tmp += S[node];
         return;
      }
      if(~L[node]) get(L[node]);
      if(~R[node]) get(R[node]);
      return;
   }

   void PrintString(){
      get(root);
      cout << tmp << endl;
      tmp.resize(0);
      return;
   }

   void init_build(ll _n, bool intialization = 0, string T = ""){

      // Server.init_build(_n, intialization, T);

      if(!intialization){
         get(root);
         swap(T, tmp);
         n += counter - del; 
         N = (n + unit_size - 1) / unit_size; SQRT = sqrt(N) + 1;
      }else{
         n = T.size();
         N = (n + unit_size - 1) / unit_size; SQRT = sqrt(N) + 1;
      }

      assert(n == T.size());
      for(ll i = 0; i < T.size(); i+= unit_size){
         temp.push_back(""); ll sz = temp.size();
         for(ll j = i; j < min(n, i + unit_size); j++) temp[sz - 1] += T[j];
      }
      
      cur = 0; counter = 0; del = 0; cur_mx = 0;
      LG = log2(N) + 1;
      L.resize(1); R.resize(1); hash.resize(1);
      par.resize(1); sum.resize(1); S.resize(1);

      root = build(1, N);
      temp.resize(0);
      tmp.resize(0);
   }

   ii kth_element(ll node, ll k){
      if(L[node] == -1) return {node, k};
      if(sum[L[node]] < k){
         return kth_element(R[node], k - sum[L[node]]);
      }
      return kth_element(L[node], k);
   }

   void Update_ancestors(ll NODE){
      ll depth = 0;
      while(NODE != -1){
         depth++;
         if(L[NODE] + R[NODE] == -2){
            NODE = par[NODE];
            continue;
         }
         if(L[NODE] == -1 || R[NODE] == -1){
            ll c = (L[NODE] == -1 ? R[NODE] : L[NODE]);
            if(NODE == root){
               root = c;
               par[root] = -1;
               return;
            }
            ll parent = par[NODE];
            if(L[parent] == NODE) L[parent] = c;
            if(R[parent] == NODE) R[parent] = c;
            par[c] = parent;
            NODE = parent;
            continue;
         }
         hash[NODE] = HASH(hash[L[NODE]], hash[R[NODE]]);
         sum[NODE] = sum[L[NODE]] + sum[R[NODE]];
         NODE = par[NODE];
      }
      cur_mx = max(depth, cur_mx);
      Mx_depth = max(Mx_depth, depth);
      return;
   }

   void insert(ll x, string h){

      if(x < 0 || x > n + counter - del){
         cout << "ERROR INSERT: INDEX NOT FOUND" << endl;
         return;
      }

      // Server.insert(x, h);

      auto [NODE, pos] = kth_element(root, max(1LL, x));
      
      string T = ""; pos = pos - (x == 0);

      for(ll i = 0; i < pos; i++) T += S[NODE][i];
      T += h;
      for(ll i = pos; i < S[NODE].size(); i++) T += S[NODE][i];

      ll _N = (T.size() + unit_size - 1) / unit_size;

      for(ll i = 0; i < T.size(); i+= unit_size){
         temp.push_back(""); ll sz = temp.size();
         for(ll j = i; j < min((ll)T.size(), i + unit_size); j++) temp[sz - 1] += T[j];
      }
      N += (_N - 1);

      ll g1 = cur + 1;

      ll c = build(1, _N);

      R[NODE] = c;
      par[c] = NODE;

      temp.resize(0);

      // updating the ancestors
      Update_ancestors(g1);

      counter += h.size();
      if(cur_mx > Constant_Factor * SQRT + 2 * LG){
         
         init_build(N);
         C++;
      }
   }

   void Delete(ll l, ll r){

      if(l < 0 || r > n + counter - del || r < l){
         cout << "ERROR DELETE: INDEX NOT FOUND" << endl;
         return;
      }

      // Server.Delete(l, r);
      
     
      auto [N1, p1] = kth_element(root, l);
      auto [N2, p2] = kth_element(root, r);

      string h = "";
      for(ll i = 0; i < p1 - 1; i++) h += S[N1][i];
      for(ll i = p2; i < S[N2].size(); i++) h += S[N2][i];

      ll rem = (r - l + 1) + h.size();

      del += rem;

      l -= p1;

      while(rem > 0){
         auto [NODE, pos] = kth_element(root, l + 1);
         assert(pos == 1); N--;
         rem -= S[NODE].size();
         while(NODE != root){
            ll parent = par[NODE];
            if(L[parent] == NODE) L[parent] = -1;
            if(R[parent] == NODE) R[parent] = -1;
            sum[parent] -= sum[NODE];
            if(sum[parent] == 0){
               NODE = parent;
            }else{
               break;
            }
         }
         // updating the ancestors
         Update_ancestors(NODE);
      }
      if(N == 0){
         init_build((ll)h.size(), 1, h);
         return;
      }
      assert(rem == 0);
      insert(l, h);
      return;
   }

   void update(ll l, ll r, string h){

      // Server.update(l, r, h);
      
      Delete(l, r);
      insert(l - 1, h);
      
      return;
   }

   

   bool Auditing(int blockID, string seed){

      auto [NODE, pos] = kth_element(root, blockID);

      /*
      Asking server to add the string seed to the end of the block with the
      given id, and return its hash
      */

      string curHash_Server = Server.GetBlockHash(NODE, seed);
      string curHash_Client = file_HASH(S[NODE] + seed);

      while(NODE != root){
        
         int parent = par[NODE];
         string siblingHash_Server;
         string siblingHash_Client;

         /* 
         asking the server to return the hash of the sibling of the node
         */

         if(L[parent] == NODE) {
            siblingHash_Server = Server.GetNodeHash(R[parent]);
            siblingHash_Client = hash[R[parent]];
         } else {
            siblingHash_Server = Server.GetNodeHash(L[parent]);
            siblingHash_Client = hash[L[parent]];
         }

         /*
          calculating the hash of the parent node from its child nodes
          here HASH() should be replaced with SHA256
         */
         curHash_Server = HASH(curHash_Server, siblingHash_Server);
         curHash_Client = HASH(curHash_Client, siblingHash_Client);
         NODE = par[NODE];
      }

      return (curHash_Server == curHash_Client);
   }
}T;

void solve(){

   

   {// File Input, delete this part of the code if not necessary
      
      cout << "Enter intial string size:\n"; clean;
      ll n; cin >> n;

      cout << "Enter number of Queries:\n"; clean;
      ll q; cin >> q;

      cout << "Enter the intial string:\n"; clean;
      string s; cin >> s;
      clean;

      T.init_build(n, 1, s);

      cout << "\n\n";

      cout << "Query Types:\n";
      cout << "Insert <int x> <string c>\n";
      cout << "Update <int l> <int r> <string c>\n";
      cout << "Delete <int l> <int r>\n";
      cout << "Auditing <int x> <string seed>\n";
      cout << "BlockCount\n";
      cout << "PrintString\n";

      cout << "\n";

      cout << "Enter Your Queries\n";

      clean;


      for(ll i = 1; i <= q; i++){
         string S; cin >> S;
         if(S == "Insert"){
            ll x; string c;
            cin >> x >> c;
            T.insert(x, c); 
         }
         if(S == "Update"){
            ll l, r; string s; cin >> l >> r >> s;
            T.update(l, r, s); 
         }
         if(S == "Delete"){
            ll l, r; cin >> l >> r;
            T.Delete(l, r);
         }
         if(S == "Auditing"){
            ll x; string seed; cin >> x >> seed;
           // cout << T.Auditing(x, seed) << endl;
         }
         if(S == "BlockCount"){
            cout << T.N << endl;
         }
         if(S == "PrintString"){
            T.PrintString();
         }
         
      }
   }

   cout << "Total Rebuild: " << C << '\n';
   cout << "Max depth: " << Mx_depth << '\n';
   cout << "Limiting Factor: " << T.Constant_Factor * T.SQRT + 2 * T.LG << '\n';
   
   return;
}

int main() {
    
    
     #ifdef LOCAL
        //freopen("in.txt", "r", stdin);
        //freopen("out.txt", "w", stdout);
        auto start_time = clock();
    #else 
       ios_base::sync_with_stdio(0); cin.tie(NULL); cout.tie(NULL);
    #endif

    //pre();
 
    ll T = 1, CT = 0; //cin >> T; 
 
    while(T--){
        // cout << "Case #" << ++CT << ": ";
        solve();
    }
    #ifdef LOCAL
        auto end_time = clock();
        cerr<< "Execution time: "<<(end_time - start_time)*(int)1e3/CLOCKS_PER_SEC<<" ms\n";
    #endif
 
    return 0;
} 