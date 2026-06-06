#include <bits/stdc++.h>
using namespace std;

map<string, vector<vector<string>>> grammar;
map<string, set<string>> FIRST, FOLLOW;
vector<string> terminals = {"id", "+", "*", "(", ")", "$"};
string startSymbol = "E";

set<string> computeFirst(string);

set<string> firstOfProduction(const vector<string>& prod) {
    set<string> res;
    bool eps = true;

    for (auto s : prod) {
        auto f = computeFirst(s);
        for (auto x : f)
            if (x != "ep") res.insert(x);
        if (!f.count("ep")) {
            eps = false;
            break;
        }
    }
    if (eps) res.insert("ep");
    return res;
}

set<string> computeFirst(string symbol) {
    if (symbol == "ep") return {"ep"};
    if (find(terminals.begin(), terminals.end(), symbol) != terminals.end()) return {symbol};
    if (FIRST.count(symbol)) return FIRST[symbol];

    set<string> res;
    for (auto prod : grammar[symbol]) {
        bool eps = true;
        for (auto s : prod) {
            auto f = computeFirst(s);
            for (auto x : f)
                if (x != "ep") res.insert(x);
            if (!f.count("ep")) {
                eps = false;
                break;
            }
        }
        if (eps) res.insert("ep");
    }
    FIRST[symbol] = res;
    return res;
}

void computeFollow() {
    FOLLOW[startSymbol].insert("$");
    bool changed = true;

    while (changed) {
        changed = false;
        for (auto &g : grammar) {
            string A = g.first;
            for (auto &prod : g.second) {
                for (int i = 0; i < prod.size(); i++) {
                    string B = prod[i];
                    if (!grammar.count(B)) continue;

                    set<string> trailer;
                    bool eps = true;
                    for (int j = i + 1; j < prod.size(); j++) {
                        auto f = computeFirst(prod[j]);
                        for (auto x : f)
                            if (x != "ep") trailer.insert(x);
                        if (!f.count("ep")) {
                            eps = false;
                            break;
                        }
                    }
                    if (eps)
                        trailer.insert(FOLLOW[A].begin(), FOLLOW[A].end());

                    int before = FOLLOW[B].size();
                    FOLLOW[B].insert(trailer.begin(), trailer.end());
                    if (FOLLOW[B].size() != before)
                        changed = true;
                }
            }
        }
    }
}

void printTable(map<string, map<string, vector<string>>> &table) {
    cout << "\nPredictive Parsing Table:\n";
    cout << left << setw(10) << "M";
    for (auto t : terminals) {
        if (t != "ep") cout << setw(15) << t;
    }
    cout << "\n";
    for (auto &g : grammar) {
        string A = g.first;
        cout << left << setw(10) << A;
        for (auto t : terminals) {
            if (t == "ep") continue;
            string entry = "";
            if (table[A].count(t)) {
                entry = A + " -> ";
                for (auto s : table[A][t]) {
                    entry += s;
                    if(s != table[A][t].back()) entry += " ";
                }
            }
            cout << setw(15) << entry;
        }
        cout << "\n";
    }
}

map<string, map<string, vector<string>>> buildTable() {
    map<string, map<string, vector<string>>> table;
    for (auto &g : grammar) {
        string A = g.first;
        for (auto &prod : g.second) {
            auto f = firstOfProduction(prod);
            for (auto t : f) {
                if (t != "ep") table[A][t] = prod;
            }
            if (f.count("ep")) {
                for (auto t : FOLLOW[A]) table[A][t] = prod;
            }
        }
    }
    return table;
}

bool parse(const vector<string>& input, map<string, map<string, vector<string>>> &table) {
    stack<string> st;
    st.push("$");
    st.push(startSymbol);
    int i = 0;

    cout << "\n" << left << setw(20) << "Stack" << setw(20) << "Input" << "Production\n";
    cout << string(60, '-') << "\n";
    
    while (!st.empty()) {
        if (i >= (int)input.size()) return false;
        
        string top = st.top();
        st.pop();
        
        // build stack string
        string st_str = "";
        stack<string> temp = st;
        vector<string> temp_v;
        while (!temp.empty()) { temp_v.push_back(temp.top()); temp.pop(); }
        for (int k = temp_v.size()-1; k >= 0; k--) st_str += temp_v[k] + " ";
        st_str += top;
        
        // build input string
        string inp_str = "";
        for (int k = i; k < (int)input.size(); k++) inp_str += input[k] + " ";
        
        cout << left << setw(20) << st_str << setw(20) << inp_str;
        
        if (top == input[i]) {
            if (top == "$") {
                cout << "Accept\n";
                return true;
            } else {
                cout << "pop\n";
                i++;
            }
        }
        else if (grammar.count(top)) {
            if (table[top].count(input[i])) {
                auto prod = table[top][input[i]];
                string prod_str = top + " -> ";
                for (auto s : prod) prod_str += s;
                cout << prod_str << "\n";
                
                for (int j = (int)prod.size() - 1; j >= 0; j--)
                    if (prod[j] != "ep") st.push(prod[j]);
            } else {
                cout << "error\n";
                return false;
            }
        }
        else {
            cout << "error\n";
            return false;
        }
    }
    return i == (int)input.size();
}

int main() {
    startSymbol = "E";

    terminals = {"id", "+", "*", "(", ")", "$"};

    grammar["E"]  = {{"T", "E'"}};
    grammar["E'"] = {{"ep"}, {"+", "T", "E'"}};
    grammar["T"]  = {{"F", "T'"}};
    grammar["T'"] = {{"ep"}, {"*", "F", "T'"}};
    grammar["F"]  = {{"id"}, {"(", "E", ")"}};

    for (auto &g : grammar)
        computeFirst(g.first);

    computeFollow();

    cout << "FIRST sets:\n";
    for (auto &p : FIRST) {
        cout << p.first << " = { ";
        for (auto x : p.second) cout << x << " ";
        cout << "}\n";
    }

    cout << "\nFOLLOW sets:\n";
    for (auto &p : FOLLOW) {
        cout << p.first << " = { ";
        for (auto x : p.second) cout << x << " ";
        cout << "}\n";
    }

    auto table = buildTable();
    printTable(table);

    vector<string> input = {"id", "+", "id","$"};
    parse(input, table);

    return 0;
}
