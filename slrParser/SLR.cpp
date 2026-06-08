#include <bits/stdc++.h>

using namespace std;

struct Production {
    string lhs;
    vector<string> rhs;
};

struct Item {
    int prodNo;
    int dotPos;
    bool operator<(const Item& other) const {
        if (prodNo != other.prodNo) return prodNo < other.prodNo;
        return dotPos < other.dotPos;
    }
    bool operator==(const Item& other) const {
        return prodNo == other.prodNo && dotPos == other.dotPos;
    }
};

struct State {
    set<Item> items;
    bool operator==(const State& other) const {
        return items == other.items;
    }
};

vector<Production> prods;
map<string, set<string>> FIRST;
map<string, set<string>> FOLLOW;
vector<State> states;

map<int, map<string, string>> ACTION;
map<int, map<string, int>> GOTO_TABLE;

set<string> non_terminals;
vector<string> ordered_nt;
set<string> terminals;
vector<string> ordered_t;

bool isNonTerminal(const string& s) {
    return non_terminals.count(s) > 0;
}

void loadGrammar(map<string, vector<vector<string>>>& grammar, const string& start_symbol) {
    non_terminals.insert(start_symbol);
    for (auto& pair : grammar) {
        non_terminals.insert(pair.first);
    }
    
    // Add augmented production
    string augmented_start = start_symbol + "'";
    non_terminals.insert(augmented_start);
    ordered_nt.push_back(augmented_start);
    ordered_nt.push_back(start_symbol);
    
    prods.push_back({augmented_start, {start_symbol}});
    
    vector<string> order = {start_symbol};
    set<string> visited_nt = {start_symbol};
    set<string> visited_t;
    
    for (size_t i = 0; i < order.size(); ++i) {
        string curr = order[i];
        if (grammar.count(curr)) {
            for (auto& rhs : grammar[curr]) {
                prods.push_back({curr, rhs});
                for (auto& symbol : rhs) {
                    if (symbol != "ep" && grammar.count(symbol) > 0) {
                        if (visited_nt.insert(symbol).second) {
                            order.push_back(symbol);
                            ordered_nt.push_back(symbol);
                        }
                    } else if (symbol != "ep" && grammar.count(symbol) == 0) {
                        if (visited_t.insert(symbol).second) {
                            ordered_t.push_back(symbol);
                            terminals.insert(symbol);
                        }
                    }
                }
            }
        }
    }
    ordered_t.push_back("$");
    terminals.insert("$");
}

void closure(State& state) {
    bool changed = true;
    while (changed) {
        changed = false;
        set<Item> new_items = state.items;
        for (const auto& item : state.items) {
            // Treat epsilon "ep" as if it has size 0 when looking for dot position
            if (item.dotPos < prods[item.prodNo].rhs.size()) {
                string B = prods[item.prodNo].rhs[item.dotPos];
                if (B != "ep" && isNonTerminal(B)) {
                    for (int i = 0; i < prods.size(); ++i) {
                        if (prods[i].lhs == B) {
                            Item new_item = {i, 0};
                            if (new_items.insert(new_item).second) {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        state.items = new_items;
    }
}

State gotoState(const State& state, const string& X) {
    State next_state;
    for (const auto& item : state.items) {
        if (item.dotPos < prods[item.prodNo].rhs.size()) {
            string symbol = prods[item.prodNo].rhs[item.dotPos];
            if (symbol == X) {
                next_state.items.insert({item.prodNo, item.dotPos + 1});
            }
        }
    }
    closure(next_state);
    return next_state;
}

void buildCanonical() {
    State start;
    start.items.insert({0, 0});
    closure(start);
    states.push_back(start);
    
    bool changed = true;
    while (changed) {
        changed = false;
        for (size_t i = 0; i < states.size(); ++i) {
            vector<string> symbols;
            for (const auto& nt : ordered_nt) symbols.push_back(nt);
            for (const auto& t : ordered_t) symbols.push_back(t);
            
            for (const string& X : symbols) {
                if (X == "ep" || X == "$") continue;
                State next_state = gotoState(states[i], X);
                if (next_state.items.empty()) continue;
                
                auto it = find(states.begin(), states.end(), next_state);
                if (it == states.end()) {
                    states.push_back(next_state);
                    changed = true;
                }
            }
        }
    }
}

void addFirst(const string& A, const string& terminal, bool& changed) {
    if (FIRST[A].insert(terminal).second) changed = true;
}

void computeFIRST() {
    for (const string& t : terminals) {
        if (t != "ep") FIRST[t].insert(t);
    }
    FIRST["ep"].insert("ep");
    
    bool changed = true;
    while (changed) {
        changed = false;
        for (const auto& prod : prods) {
            if (prod.rhs.empty() || (prod.rhs.size() == 1 && prod.rhs[0] == "ep")) {
                addFirst(prod.lhs, "ep", changed);
                continue;
            }
            
            bool all_have_epsilon = true;
            for (const string& symbol : prod.rhs) {
                for (const string& f : FIRST[symbol]) {
                    if (f != "ep") addFirst(prod.lhs, f, changed);
                }
                if (FIRST[symbol].count("ep") == 0) {
                    all_have_epsilon = false;
                    break;
                }
            }
            if (all_have_epsilon) {
                addFirst(prod.lhs, "ep", changed);
            }
        }
    }
}

void addFollow(const string& A, const string& terminal, bool& changed) {
    if (FOLLOW[A].insert(terminal).second) changed = true;
}

void computeFOLLOW() {
    FOLLOW[prods[0].lhs].insert("$");
    FOLLOW[prods[1].lhs].insert("$"); // Start symbol (first real production)
    
    bool changed = true;
    while (changed) {
        changed = false;
        for (const auto& prod : prods) {
            for (size_t i = 0; i < prod.rhs.size(); ++i) {
                const string& B = prod.rhs[i];
                if (!isNonTerminal(B)) continue;
                
                bool all_next_have_epsilon = true;
                for (size_t j = i + 1; j < prod.rhs.size(); ++j) {
                    const string& next_symbol = prod.rhs[j];
                    for (const string& f : FIRST[next_symbol]) {
                        if (f != "ep") addFollow(B, f, changed);
                    }
                    if (FIRST[next_symbol].count("ep") == 0) {
                        all_next_have_epsilon = false;
                        break;
                    }
                }
                
                if (all_next_have_epsilon) {
                    for (const string& f : FOLLOW[prod.lhs]) {
                        addFollow(B, f, changed);
                    }
                }
            }
        }
    }
}

void buildSLR() {
    for (size_t i = 0; i < states.size(); ++i) {
        for (const auto& item : states[i].items) {
            bool is_epsilon_prod = (prods[item.prodNo].rhs.size() == 1 && prods[item.prodNo].rhs[0] == "ep");
            
            if (!is_epsilon_prod && item.dotPos < prods[item.prodNo].rhs.size()) {
                string a = prods[item.prodNo].rhs[item.dotPos];
                State next_state = gotoState(states[i], a);
                auto it = find(states.begin(), states.end(), next_state);
                if (it != states.end()) {
                    int j = distance(states.begin(), it);
                    if (!isNonTerminal(a)) {
                        /* Check for shift-reduce conflict */
                        if (ACTION[i].count(a) == 0 || ACTION[i][a][0] == 's') {
                            ACTION[i][a] = "s" + to_string(j);
                        } else {
                            cout << "Warning: Shift-Reduce conflict at state " << i << " on symbol " << a << "\n";
                        }
                    } else {
                        GOTO_TABLE[i][a] = j;
                    }
                }
            } else {
                if (item.prodNo == 0) {
                    ACTION[i]["$"] = "acc";
                } else {
                    for (const string& f : FOLLOW[prods[item.prodNo].lhs]) {
                        if (ACTION[i].count(f) == 0 || ACTION[i][f][0] == 'r') {
                            ACTION[i][f] = "r" + to_string(item.prodNo);
                        } else {
                            cout << "Warning: Shift-Reduce conflict at state " << i << " on symbol " << f << "\n";
                        }
                    }
                }
            }
        }
    }
}

string formatSet(const set<string>& s) {
    string res = "{";
    bool first = true;
    for (const string& x : s) {
        if (!first) res += ",";
        res += x;
        first = false;
    }
    res += "}";
    return res;
}

void printFirstFollow() {
    cout << "=== FIRST and FOLLOW Sets ===\n\n";
    int w_nt = 15;
    int w_set = 20;

    cout << left << setw(w_nt) << "Nonterminal" 
         << " | " << setw(w_set) << "FIRST" 
         << " | " << "FOLLOW" << "\n";
    cout << string(w_nt, '-') << "-+-" << string(w_set, '-') << "-+-" << string(w_set, '-') << "\n";

    for (const string& nt : ordered_nt) {
        cout << left << setw(w_nt) << nt 
             << " | " << setw(w_set) << formatSet(FIRST[nt]) 
             << " | " << formatSet(FOLLOW[nt]) << "\n";
    }
    cout << "\n";
}

void printParsingTable() {
    vector<string> action_cols = ordered_t;
    vector<string> goto_cols = ordered_nt;
    
    int cell_w = 4;
    
    cout << "\n=== Parsing Table ===\n\n";
    
    int action_w = action_cols.size() * cell_w + action_cols.size() - 1;
    int goto_w   = goto_cols.size() * cell_w + goto_cols.size() - 1;
    
    // Header row 1
    cout << left << setw(8) << "State" << " | ";
    cout << left << setw(action_w) << "ACTION" << " | ";
    cout << left << setw(goto_w) << "GOTO" << "\n";
    
    // Separators
    cout << string(8, '-') << "-+-";
    cout << string(action_w, '-') << "-+-";
    cout << string(goto_w, '-') << "\n";
    
    // Header row 2
    cout << left << setw(8) << "" << " | ";
    for (size_t i = 0; i < action_cols.size(); ++i) {
        cout << left << setw(cell_w) << action_cols[i];
        if (i + 1 < action_cols.size()) cout << " ";
    }
    cout << " | ";
    for (size_t i = 0; i < goto_cols.size(); ++i) {
        cout << left << setw(cell_w) << goto_cols[i];
        if (i + 1 < goto_cols.size()) cout << " ";
    }
    cout << "\n";
    
    // Separators
    cout << string(8, '-') << "-+-";
    cout << string(action_w, '-') << "-+-";
    cout << string(goto_w, '-') << "\n";
    
    // rows
    for (size_t i = 0; i < states.size(); ++i) {
        cout << left << setw(8) << i << " | ";
        
        // ACTION columns
        for (size_t j = 0; j < action_cols.size(); ++j) {
            string val = "";
            if (ACTION[i].count(action_cols[j])) {
                val = ACTION[i][action_cols[j]];
            }
            cout << left << setw(cell_w) << val;
            if (j + 1 < action_cols.size()) cout << " ";
        }
        cout << " | ";
        
        // GOTO columns
        for (size_t j = 0; j < goto_cols.size(); ++j) {
            string val = "";
            if (GOTO_TABLE[i].count(goto_cols[j]) && GOTO_TABLE[i][goto_cols[j]] != -1) {
                val = to_string(GOTO_TABLE[i][goto_cols[j]]);
            }
            cout << left << setw(cell_w) << val;
            if (j + 1 < goto_cols.size()) cout << " ";
        }
        cout << "\n";
    }
    cout << "\n";
}

// Utility to generate formatted stack string with alternating numbers and symbols
string get_stack_str(const vector<int>& state_stack, const vector<string>& symbol_stack, bool intermediate = false, string goto_lhs = "") {
    string res = to_string(state_stack[0]);
    for (size_t i = 0; i < symbol_stack.size(); ++i) {
        res += " " + symbol_stack[i] + " " + to_string(state_stack[i+1]);
    }
    if (intermediate) {
        res += " " + goto_lhs;
    }
    return res;
}

void parse(const vector<string>& input_tokens) {
    vector<int> state_stack;
    vector<string> symbol_stack;
    
    state_stack.push_back(0);
    int ip = 0;
    
    int W_STEP   = 5;
    int W_STACK  = 35;
    int W_INPUT  = 25;
    int W_ACTION = 10;
    int step = 1;

    cout << "=== Parsing Trace ===\n\n";
    cout << left << setw(W_STEP) << "Step" << " | " << setw(W_STACK) << "Stack" << " | " << setw(W_INPUT) << "Input" << " | " << setw(W_ACTION) << "Action" << "\n";
    cout << string(W_STEP, '-') << "-+-" << string(W_STACK, '-') << "-+-" << string(W_INPUT, '-') << "-+-" << string(W_ACTION, '-') << "\n";

    while (true) {
        int state = state_stack.back();
        string a = input_tokens[ip];
        
        string inpBuf = "";
        for (size_t i = ip; i < input_tokens.size(); ++i) inpBuf += input_tokens[i] + " ";
        
        string act = ACTION[state][a];
        
        if (act.empty()) {
            cout << left << setw(W_STEP) << step++ << " | " << setw(W_STACK) << get_stack_str(state_stack, symbol_stack) << " | " << setw(W_INPUT) << inpBuf << " | " << setw(W_ACTION) << "ERROR" << "\n";
            break;
        } else if (act[0] == 's') {
            int next_state = stoi(act.substr(1));
            cout << left << setw(W_STEP) << step++ << " | " << setw(W_STACK) << get_stack_str(state_stack, symbol_stack) << " | " << setw(W_INPUT) << inpBuf << " | " << setw(W_ACTION) << ("s" + to_string(next_state)) << "\n";
            
            symbol_stack.push_back(a);
            state_stack.push_back(next_state);
            ip++;
        } else if (act[0] == 'r') {
            int p = stoi(act.substr(1));
            cout << left << setw(W_STEP) << step++ << " | " << setw(W_STACK) << get_stack_str(state_stack, symbol_stack) << " | " << setw(W_INPUT) << inpBuf << " | " << setw(W_ACTION) << ("r" + to_string(p)) << "\n";
            
            int rlen = prods[p].rhs.size();
            bool is_epsilon = (rlen == 1 && prods[p].rhs[0] == "ep");
            if (is_epsilon) rlen = 0;
            
            for (int i = 0; i < rlen; ++i) {
                state_stack.pop_back();
                symbol_stack.pop_back();
            }
            
            int top = state_stack.back();
            int gt = GOTO_TABLE[top][prods[p].lhs];
            
            // Print the intermediate GOTO step matching trace format
            cout << left << setw(W_STEP) << step++ << " | " << setw(W_STACK) << get_stack_str(state_stack, symbol_stack, true, prods[p].lhs) << " | " << setw(W_INPUT) << inpBuf << " | " << setw(W_ACTION) << to_string(gt) << "\n";
            
            symbol_stack.push_back(prods[p].lhs);
            state_stack.push_back(gt);
        } else if (act == "acc") {
            cout << left << setw(W_STEP) << step++ << " | " << setw(W_STACK) << get_stack_str(state_stack, symbol_stack) << " | " << setw(W_INPUT) << inpBuf << " | " << setw(W_ACTION) << "acc" << "\n";
            break;
        }
    }
}

int main() {
    map<string, vector<vector<string>>> grammar;
    
    // grammar["S"]={{"(","L",")"}}; 
    // grammar["L"]={{"L",",","id"},{"id"}};

    // grammar["E'"] = {{"E"}};
    grammar["E"] = {{"E", "+", "T"},{"T"}};
    grammar["T"] = {{"T", "*", "F"},{"F"}};
    grammar["F"] = {{"(", "E", ")"},{"id"}};
        
    loadGrammar(grammar, "E");
    
    // Ensure the Augmented Grammar Prints First
    cout << "=== Augmented Grammar ===\n";
    for (size_t i = 0; i < prods.size(); ++i) {
        cout << "  " << i << ". " << prods[i].lhs << " -> ";
        for (const string& s : prods[i].rhs) cout << s << " ";
        cout << "\n";
    }
    
    computeFIRST();
    computeFOLLOW();
    printFirstFollow();
    buildCanonical();
    buildSLR();
    
    // Print Parsing Table Matrix just before input trace
    printParsingTable();
    
    // vector<string> input = {"(", "id", ",", "id", ",", "id", ")", "$"};
    vector<string> input = {"id", "+", "id", "*", "id", "$"};
    parse(input);
    
    return 0;
}