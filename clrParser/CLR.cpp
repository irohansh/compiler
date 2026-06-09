#include <bits/stdc++.h>

using namespace std;

// Represents a grammar production rule with a LHS and multiple RHS symbols
struct Production {
    string lhs;
    vector<string> rhs;
};

// Represents an LR(1) item: A -> α.β, a
// prodNo: Index of the production in `prods`
// dotPos: Position of the dot '.' in the RHS
// lookahead: The lookahead terminal symbol
struct Item {
    int prodNo;
    int dotPos;
    string lookahead;
    bool operator<(const Item& other) const {
        if (prodNo != other.prodNo) return prodNo < other.prodNo;
        if (dotPos != other.dotPos) return dotPos < other.dotPos;
        return lookahead < other.lookahead;
    }
    bool operator==(const Item& other) const {
        return prodNo == other.prodNo && dotPos == other.dotPos && lookahead == other.lookahead;
    }
};

// Represents a canonical state containing a set of LR(1) items
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

// Checks if a given symbol is a non-terminal symbol
bool isNonTerminal(const string& s) {
    return non_terminals.count(s) > 0;
}

// Loads the grammar, adds augmented production, separates terminals and non-terminals,
// and ensures variables are stored in ordered lists for consistent printing
void loadGrammar(map<string, vector<vector<string>>>& grammar, const string& start_symbol) {
    non_terminals.insert(start_symbol);
    for (auto& pair : grammar) {
        non_terminals.insert(pair.first);
    }
    
    // Add augmented production: start_symbol' -> start_symbol
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

// Utility to insert a terminal into a FIRST set and detect if the set grew
void addFirst(const string& A, const string& terminal, bool& changed) {
    if (FIRST[A].insert(terminal).second) changed = true;
}

// Computes FIRST sets for all terminal and non-terminal symbols
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

// Utility to insert a terminal into a FOLLOW set and detect if the set grew
void addFollow(const string& A, const string& terminal, bool& changed) {
    if (FOLLOW[A].insert(terminal).second) changed = true;
}

// Computes FOLLOW sets for all non-terminal symbols
void computeFOLLOW() {
    FOLLOW[prods[0].lhs].insert("$");
    FOLLOW[prods[1].lhs].insert("$"); 
    
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

// Calculates FIRST set for a sequence of symbols string (e.g. βa in rule A -> α.Bβ, a)
set<string> getFirstOfString(const vector<string>& seq) {
    set<string> res;
    bool all_have_ep = true;
    for (const string& symbol : seq) {
        for (const string& f : FIRST[symbol]) {
            if (f != "ep") res.insert(f);
        }
        if (FIRST[symbol].count("ep") == 0) {
            all_have_ep = false;
            break;
        }
    }
    if (all_have_ep) res.insert("ep");
    return res;
}

// Calculates the closure for a given state by recursively generating LR(1) items
// Includes propagating lookahead symbols based on the remaining RHS symbols
void closure(State& state) {
    bool changed = true;
    while (changed) {
        changed = false;
        set<Item> new_items = state.items;
        for (const auto& item : state.items) {
            if (item.dotPos < prods[item.prodNo].rhs.size()) {
                string B = prods[item.prodNo].rhs[item.dotPos];
                if (B != "ep" && isNonTerminal(B)) {
                    vector<string> seq;
                    for (size_t k = item.dotPos + 1; k < prods[item.prodNo].rhs.size(); ++k) {
                        seq.push_back(prods[item.prodNo].rhs[k]);
                    }
                    seq.push_back(item.lookahead);
                    
                    set<string> first_res = getFirstOfString(seq);
                    
                    for (int i = 0; i < prods.size(); ++i) {
                        if (prods[i].lhs == B) {
                            for (const string& lookahead : first_res) {
                                Item new_item = {i, 0, lookahead};
                                if (new_items.insert(new_item).second) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        state.items = new_items;
    }
}

// Performs the GOTO operation on a state with a transition symbol X, driving the parsing automaton
State gotoState(const State& state, const string& X) {
    State next_state;
    for (const auto& item : state.items) {
        if (item.dotPos < prods[item.prodNo].rhs.size()) {
            string symbol = prods[item.prodNo].rhs[item.dotPos];
            if (symbol == X) {
                next_state.items.insert({item.prodNo, item.dotPos + 1, item.lookahead});
            }
        }
    }
    closure(next_state);
    return next_state;
}

// Builds the Canonical Collection of sets of LR(1) items
void buildCanonical() {
    State start;
    start.items.insert({0, 0, "$"});
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

// Constructs the Canonical LR (CLR) parsing tables (ACTION and GOTO) from generated states
void buildCLR() {
    for (size_t i = 0; i < states.size(); ++i) {
        for (const auto& item : states[i].items) {
            bool is_epsilon_prod = (prods[item.prodNo].rhs.size() == 1 && prods[item.prodNo].rhs[0] == "ep");
            
            if (!is_epsilon_prod && item.dotPos < prods[item.prodNo].rhs.size()) {
                // Determine shift operation mapping
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
                        // Register corresponding GOTO mappings
                        GOTO_TABLE[i][a] = j;
                    }
                }
            } else {
                // Resolve reducible and acceptance states
                if (item.prodNo == 0) {
                    if (item.lookahead == "$") {
                        ACTION[i]["$"] = "acc";
                    }
                } else {
                    string f = item.lookahead;
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

// Formats a `set<string>` as an elegant visual representation, eg: {a,b,c}
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

// Pretty-prints the computed FIRST and FOLLOW Sets for output verification
void printFirstFollow() {
    cout << "=== FIRST and FOLLOW Sets ===\n\n";
    int w_nt = -15;
    int w_set = -20;
    
    // Simple printf is better for negative width
    printf("%*s | %*s | %s\n", w_nt, "Nonterminal", w_set, "FIRST", "FOLLOW");
    for(int i=0; i<15; i++) printf("-"); printf("-+-");
    for(int i=0; i<20; i++) printf("-"); printf("-+-");
    for(int i=0; i<20; i++) printf("-"); printf("\n");
    
    for (const string& nt : ordered_nt) {
        char fst[256], fol[256];
        strcpy(fst, formatSet(FIRST[nt]).c_str());
        strcpy(fol, formatSet(FOLLOW[nt]).c_str());
        printf("%*s | %*s | %s\n", w_nt, nt.c_str(), w_set, fst, fol);
    }
    cout << "\n";
}

// Pretty-prints ACTION and GOTO rules composing the Parsing Table 
void printParsingTable() {
    vector<string> action_cols = ordered_t;
    vector<string> goto_cols = ordered_nt;
    
    int cell_w = -4;
    
    printf("=== Parsing Table ===\n\n");
    
    int action_w = action_cols.size() * abs(cell_w) + action_cols.size() - 1;
    int goto_w = goto_cols.size() * abs(cell_w) + goto_cols.size() - 1;
    
    printf("%-8s | %-*s | %s\n", "State", action_w, "ACTION", "GOTO");
    for(int i=0; i<8; i++) printf("-"); printf("-+-");
    for(int i=0; i<action_w; i++) printf("-"); printf("-+-");
    for(int i=0; i<goto_w; i++) printf("-"); printf("\n");
    
    printf("%8s | ", "");
    for (size_t i = 0; i < action_cols.size(); ++i) {
        printf("%*s", cell_w, action_cols[i].c_str());
        if (i + 1 < action_cols.size()) printf(" ");
    }
    printf(" | ");
    for (size_t i = 0; i < goto_cols.size(); ++i) {
        printf("%*s", cell_w, goto_cols[i].c_str());
        if (i + 1 < goto_cols.size()) printf(" ");
    }
    printf("\n");
    
    for(int i=0; i<8; i++) printf("-"); printf("-+-");
    for(int i=0; i<action_w; i++) printf("-"); printf("-+-");
    for(int i=0; i<goto_w; i++) printf("-"); printf("\n");
    
    for (size_t i = 0; i < states.size(); ++i) {
        printf("%-8lu | ", i);
        for (size_t j = 0; j < action_cols.size(); ++j) {
            string val = "";
            if (ACTION[i].count(action_cols[j])) {
                val = ACTION[i][action_cols[j]];
            }
            printf("%*s", cell_w, val.c_str());
            if (j + 1 < action_cols.size()) printf(" ");
        }
        printf(" | ");
        for (size_t j = 0; j < goto_cols.size(); ++j) {
            string val = "";
            if (GOTO_TABLE[i].count(goto_cols[j]) && GOTO_TABLE[i][goto_cols[j]] != -1) {
                val = to_string(GOTO_TABLE[i][goto_cols[j]]);
            }
            printf("%*s", cell_w, val.c_str());
            if (j + 1 < goto_cols.size()) printf(" ");
        }
        printf("\n");
    }
    printf("\n");
}

// Extractor helper transforming the stack into a properly laid out string literal sequence
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

// Executes generic LR(1) string parsing using action states matching stack inputs
void parse(const vector<string>& input_tokens) {
    vector<int> state_stack;
    vector<string> symbol_stack;
    
    state_stack.push_back(0);
    int ip = 0;
    
    int W_STEP   = -5;
    int W_STACK  = -35;
    int W_INPUT  = -25;
    int W_ACTION = -10;
    int step = 1;

    printf("=== Parsing Trace ===\n\n");
    printf("%*s | %*s | %*s | %s\n", W_STEP, "Step", W_STACK, "Stack", W_INPUT, "Input", "Action");
    for(int i=0;i<5;i++)printf("-");printf("-+-");
    for(int i=0;i<35;i++)printf("-");printf("-+-");
    for(int i=0;i<25;i++)printf("-");printf("-+-");
    for(int i=0;i<10;i++)printf("-");printf("\n");

    while (true) {
        int state = state_stack.back();
        string a = input_tokens[ip];
        
        string inpBuf = "";
        for (size_t i = ip; i < input_tokens.size(); ++i) inpBuf += input_tokens[i] + " ";
        
        string act = ACTION[state][a];
        
        char step_str[16];
        sprintf(step_str, "%d", step++);

        if (act.empty()) {
            // Encountered error
            printf("%*s | %*s | %*s | %s\n", W_STEP, step_str, W_STACK, get_stack_str(state_stack, symbol_stack).c_str(), W_INPUT, inpBuf.c_str(), "ERROR");
            break;
        } else if (act[0] == 's') {
            // Processing successful: shift
            int next_state = stoi(act.substr(1));
            printf("%*s | %*s | %*s | %s\n", W_STEP, step_str, W_STACK, get_stack_str(state_stack, symbol_stack).c_str(), W_INPUT, inpBuf.c_str(), act.c_str());
            
            symbol_stack.push_back(a);
            state_stack.push_back(next_state);
            ip++;
        } else if (act[0] == 'r') {
            // Processing successful: reduce
            int p = stoi(act.substr(1));
            printf("%*s | %*s | %*s | %s\n", W_STEP, step_str, W_STACK, get_stack_str(state_stack, symbol_stack).c_str(), W_INPUT, inpBuf.c_str(), act.c_str());
            
            int rlen = prods[p].rhs.size();
            bool is_epsilon = (rlen == 1 && prods[p].rhs[0] == "ep");
            if (is_epsilon) rlen = 0;
            
            for (int i = 0; i < rlen; ++i) {
                state_stack.pop_back();
                symbol_stack.pop_back();
            }
            
            int top = state_stack.back();
            int gt = GOTO_TABLE[top][prods[p].lhs];
            
            char step2_str[16];
            sprintf(step2_str, "%d", step++);
            
            string gt_str = to_string(gt);
            
            printf("%*s | %*s | %*s | %s\n", W_STEP, step2_str, W_STACK, get_stack_str(state_stack, symbol_stack, true, prods[p].lhs).c_str(), W_INPUT, inpBuf.c_str(), gt_str.c_str());
            
            symbol_stack.push_back(prods[p].lhs);
            state_stack.push_back(gt);
        } else if (act == "acc") {
            // Parsed successfully to End of File identifier
            printf("%*s | %*s | %*s | %s\n", W_STEP, step_str, W_STACK, get_stack_str(state_stack, symbol_stack).c_str(), W_INPUT, inpBuf.c_str(), "acc");
            break;
        }
    }
}

int main() {
    map<string, vector<vector<string>>> grammar;

    // Default initialization parsing rules (example)
    grammar["S"] = {{"C", "C"}};
    grammar["C"] = {{"c", "C"},{"d"}};
        
    loadGrammar(grammar, "S");
    
    cout << "=== Augmented Grammar ===\n";
    for (size_t i = 0; i < prods.size(); ++i) {
        cout << "  " << i << ". " << prods[i].lhs << " -> ";
        for (const string& s : prods[i].rhs) cout << s << " ";
        cout << "\n";
    }
    
    // Core CLR evaluation stages
    computeFIRST();
    computeFOLLOW();
    printFirstFollow();
    buildCanonical();
    buildCLR();
    
    printParsingTable();
    
    // Example test case validation
    vector<string> input = {"c", "d", "d", "$"};
    parse(input);
    
    return 0;
}
