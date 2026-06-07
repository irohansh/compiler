#include <bits/stdc++.h>

using namespace std;

map<string, vector<vector<string>>> g;
vector<string> nonTerminals;

// Function to resolve Operator Precedence conflicts explicitly
int get_priority(const string& op) {
    if (op == "^") return 3;
    if (op == "*" || op == "/") return 2;
    if (op == "+" || op == "-") return 1;
    return 0;
}

// A string is a terminal if it does not start with an uppercase letter
bool isTerminal(const string& s) {
    if (s.empty()) return false;
    return !isupper(s[0]);
}

void add_grammar(const char* lhs, ...) {
    string lhs_str(lhs);
    if (find(nonTerminals.begin(), nonTerminals.end(), lhs_str) == nonTerminals.end()) {
        nonTerminals.push_back(lhs_str);
    }
    
    va_list args;
    va_start(args, lhs);
    vector<string> rhs;
    const char* symbol;
    while ((symbol = va_arg(args, const char*)) != NULL) {
        rhs.push_back(string(symbol));
    }
    va_end(args);
    g[lhs_str].push_back(rhs);
}

// Function to determine if a terminal acts as an operator for left-associativity
bool isOperator(const string& op) {
    if (op == "id" || op == "$" || op == "(" || op == ")") return false;
    return true; // Any math operator, 'b', ',', etc. default to left-associative.
}

int main() {
    // The user's ambiguous grammar. We support it fully.
    // add_grammar("E", "E", "+", "E", NULL);
    // add_grammar("E", "E", "*", "E", NULL);
    // add_grammar("E", "id", NULL);


    // add_grammar("S", "(", "L", ")", NULL);
    // add_grammar("S", "a", NULL);
    // add_grammar("L", "L", ",", "S", NULL);
    // add_grammar("L", "S", NULL);

    // add_grammar("P", "S", "b", "P", NULL);
    // add_grammar("P", "S", NULL);
    // add_grammar("R", "b", "P", NULL);
    // add_grammar("R", "b", "S", NULL);
    // add_grammar("S", "W", "b", "S", NULL);
    // add_grammar("S", "W", NULL);
    // add_grammar("W", "L", "*", "W", NULL);
    // add_grammar("W", "L", NULL);
    // add_grammar("L", "id", NULL);

    // add_grammar("S", "a", NULL);
    // add_grammar("S", "/", NULL);
    // add_grammar("S", "(", "T", ")", NULL);
    // add_grammar("T", "T", ",", "S", NULL);
    // add_grammar("T", "S", NULL);

    add_grammar("E", "E", "+", "E", NULL);
    add_grammar("E", "E", "*", "E", NULL);
    add_grammar("E", "E", "-", "E", NULL);
    add_grammar("E", "E", "/", "E", NULL);
    add_grammar("E", "E", "^", "E", NULL);
    
    add_grammar("E", "(", "E", ")", NULL);
    add_grammar("E", "-", "E", NULL);
    add_grammar("E", "id", NULL);

    add_grammar("A", "+", NULL);
    add_grammar("A", "*", NULL);
    add_grammar("A", "-", NULL);
    add_grammar("A", "/", NULL);
    add_grammar("A", "^", NULL);


    map<string, set<string>> leading, trailing;
    bool changed = true;

    // Calculate Leading and Trailing sets structurally
    while (changed) {
        changed = false;
        for (auto &p : g) {
            string nt = p.first;
            for (auto &rhs : p.second) {
                // Leading Calculation
                for (int i = 0; i < rhs.size(); i++) {
                    if (isTerminal(rhs[i])) {
                        if (leading[nt].insert(rhs[i]).second) changed = true;
                        break;
                    } else {
                        for (const string& c : leading[rhs[i]])
                            if (leading[nt].insert(c).second) changed = true;
                        if (i + 1 < rhs.size() && isTerminal(rhs[i+1])) {
                            if (leading[nt].insert(rhs[i+1]).second) changed = true;
                        }
                        break;
                    }
                }
                
                // Trailing Calculation
                for (int i = (int)rhs.size() - 1; i >= 0; i--) {
                    if (isTerminal(rhs[i])) {
                        if (trailing[nt].insert(rhs[i]).second) changed = true;
                        break;
                    } else {
                        for (const string& c : trailing[rhs[i]])
                            if (trailing[nt].insert(c).second) changed = true;
                        if (i - 1 >= 0 && isTerminal(rhs[i-1])) {
                            if (trailing[nt].insert(rhs[i-1]).second) changed = true;
                        }
                        break;
                    }
                }
            }
        }
    }

    cout << "--- Leading and Trailing Sets ---\n";
    for (const string& nt : nonTerminals) {
        cout << "Leading(" << nt << ") = { ";
        for (const string& c : leading[nt]) cout << c << " ";
        cout << "}\n";

        cout << "Trailing(" << nt << ") = { ";
        for (const string& c : trailing[nt]) cout << c << " ";
        cout << "}\n\n";
    }

    // Collect all terminals structurally from RHS vectors
    set<string> terminals;
    for (auto &p : g) {
        for (auto &rhs : p.second) {
            for (const string& c : rhs) {
                if (isTerminal(c)) terminals.insert(c);
            }
        }
    }
    
    // Build Operator Precedence Table according strictly to textbook rules
    map<pair<string, string>, string> optable;
    for (auto &p : g) {
        for (auto &rhs : p.second) {
            for (int i = 0; i < rhs.size(); i++) {
                if (isTerminal(rhs[i])) { // Xi is a terminal
                    // Rule 3(a): Xi = Xi+1
                    if (i + 1 < rhs.size() && isTerminal(rhs[i+1])) {
                        optable[{rhs[i], rhs[i+1]}] = "=";
                    }
                    // Rule 3(b): Xi = Xi+2
                    if (i + 2 < rhs.size() && isTerminal(rhs[i+2]) && !isTerminal(rhs[i+1])) {
                        optable[{rhs[i], rhs[i+2]}] = "=";
                    }
                    // Rule 3(c): Xi < LEADING(Xi+1)
                    if (i + 1 < rhs.size() && !isTerminal(rhs[i+1])) { 
                        for (const string& c : leading[rhs[i+1]]) {
                            // Enforce Left-associativity natively for recursive identical operators
                            if (rhs[i] == c && c != "(" && c != ")" && c != "$") {
                                optable[{rhs[i], c}] = ">";
                            } else {
                                // Standard rule: if `>` is already derived, it wins
                                if (optable.count({rhs[i], c}) == 0 || optable[{rhs[i], c}] != ">") {
                                    optable[{rhs[i], c}] = "<";
                                }
                            }
                        }
                    }
                } else { // Xi is a non-terminal
                    // Rule 3(d): TRAILING(Xi) > Xi+1
                    if (i + 1 < rhs.size() && isTerminal(rhs[i+1])) { 
                        for (const string& c : trailing[rhs[i]]) {
                            optable[{c, rhs[i+1]}] = ">";
                        }
                    }
                }
            }
        }
    }

    // Rule 2: Relations with $
    if (!nonTerminals.empty()) {
        string startIndex = nonTerminals[0]; // Assuming first is start
        for (const string& c : leading[startIndex]) optable[{"$", c}] = "<";
        for (const string& c : trailing[startIndex]) optable[{c, "$"}] = ">";
    }

    // Mathematical safety resolver pass for ambiguous math grammars (e.g. E -> E+E | E*E)
    for (const string& t1 : terminals) {
        for (const string& t2 : terminals) {
            if (get_priority(t1) > 0 && get_priority(t2) > 0) {
                if (get_priority(t1) < get_priority(t2)) optable[{t1, t2}] = "<";
                else if (get_priority(t1) > get_priority(t2)) optable[{t1, t2}] = ">";
                else optable[{t1, t2}] = ">";  // Math is conventionally left-associative
            }
        }
    }

    cout << "--- Operator Precedence Table ---\n";
    cout << left << setw(4) << "";
    for (const string& t : terminals) cout << left << setw(4) << t;
    cout << left << setw(4) << "$" << "\n";
    
    for (const string& t1 : terminals) {
        cout << left << setw(4) << t1;
        for (const string& t2 : terminals) {
            string rel = optable[{t1, t2}];
            if (rel == "") rel = " ";
            cout << left << setw(4) << rel;
        }
        string rel_d = optable[{t1, "$"}];
        if (rel_d == "") rel_d = " ";
        cout << left << setw(4) << rel_d << "\n";
    }
    
    // Print $ securely last
    cout << left << setw(4) << "$";
    for (const string& t2 : terminals) {
        string rel = optable[{"$", t2}];
        if (rel == "") rel = " ";
        cout << left << setw(4) << rel;
    }
    string rel_dd = optable[{"$", "$"}];
    if (rel_dd == "") rel_dd = " ";
    cout << left << setw(4) << rel_dd << "\n";

    // Trace Simulator
    cout << "\n--- Input String Parsing (Operator Precedence) ---\n";
    // vector<string> input_tokens = {"id", "+", "id", "*", "id", "$"};
    // vector<string> input_tokens = {"(","a",",","a",")", "$"};
    // vector<string> input_tokens = {"id", "*", "id", "b", "id", "$"};
    vector<string> input_tokens = {"id", "&&", "id", "||", "id", "$"};
    
    string input_display = "";
    for(int k=0; k<input_tokens.size(); k++) {
        input_display += input_tokens[k];
        if (k != input_tokens.size() - 1) input_display += " ";
    }
    cout << "Input to parse: " << input_display << "\n\n";
    
    cout << left << setw(10) << "Step" << setw(20) << "Stack" << setw(20) << "Input" << "Action\n";
    cout << string(70, '-') << "\n";

    vector<string> st = {"$"};
    int step = 1;
    int ptr = 0;

    auto print_state = [&](const string& action) {
        string stack_str = "";
        for(const string& tk : st) stack_str += tk; // keeping stack together for readability
        
        string inp_str = "";
        for(int k=ptr; k<input_tokens.size(); k++) {
            inp_str += input_tokens[k];
            if (k != input_tokens.size() - 1) inp_str += " ";
        }
        
        cout << left << setw(10) << step++ << setw(20) << stack_str << setw(20) << inp_str << action << "\n";
    };

    while (true) {
        if (ptr >= input_tokens.size()) break;
        string a = input_tokens[ptr];
        
        int topT = st.size() - 1;
        while (topT >= 0 && !isTerminal(st[topT]) && st[topT] != "$") {
            topT--;
        }
        string topTerm = st[topT];

        if (topTerm == "$" && a == "$") {
            print_state("Accept");
            break;
        }

        string rel = optable[{topTerm, a}];
        
        if (rel == "<" || rel == "=") {
            print_state("s(" + a + ")");
            st.push_back(a);
            ptr++;
        } else if (rel == ">") {
            int terminal_idx = st.size() - 1;
            while(terminal_idx >= 0 && !isTerminal(st[terminal_idx]) && st[terminal_idx] != "$") {
                terminal_idx--;
            }
            
            int handleStart = terminal_idx;
            string currentT = st[terminal_idx];
            
            while (handleStart > 0) {
                int prevTIdx = handleStart - 1;
                while(prevTIdx >= 0 && !isTerminal(st[prevTIdx]) && st[prevTIdx] != "$") {
                    prevTIdx--;
                }
                string prevT = st[prevTIdx];
                if (optable[{prevT, currentT}] == "<") {
                    handleStart = prevTIdx + 1;
                    break;
                }
                currentT = prevT;
                handleStart = prevTIdx; // MUST step backwards strictly
            }
            
            vector<string> handle_tokens;
            string handle = "";
            for(int k = handleStart; k < st.size(); k++) {
                handle += st[k];
                handle_tokens.push_back(st[k]);
            }
            
            // Find correct LHS by matching the terminal skeleton of the handle
            string handle_skeleton = "";
            for(const string& sym : handle_tokens) {
                if (isTerminal(sym)) handle_skeleton += sym;
                else handle_skeleton += "N";
            }
            
            string reduced_lhs = nonTerminals[0]; // Fallback to start symbol
            bool foundLHS = false;
            for (auto& p : g) {
                if (foundLHS) break;
                for (auto& rhs : p.second) {
                    string prod_skeleton = "";
                    for (const string& sym : rhs) {
                        if (isTerminal(sym)) prod_skeleton += sym;
                        else prod_skeleton += "N";
                    }
                    if (prod_skeleton == handle_skeleton) {
                        reduced_lhs = p.first;
                        foundLHS = true;
                        break;
                    }
                }
            }
            
            print_state("r(" + reduced_lhs + "->" + handle + ")");
            
            st.erase(st.begin() + handleStart, st.end());
            st.push_back(reduced_lhs); 
            
        } else {
            print_state("Error");
            break;
        }
    }

    return 0;
}
