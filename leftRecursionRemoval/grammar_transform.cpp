#include <bits/stdc++.h>

using namespace std;

// Type alias to make code cleaner
using Production = vector<string>;
using Grammar = map<string, vector<Production>>;

// Helper function to print the grammar
void printGrammar(const Grammar& grammar, const string& startSymbol = "S") {
    // Print the start symbol first if it exists
    if (grammar.count(startSymbol)) {
        cout << startSymbol << " -> ";
        const auto& productions = grammar.at(startSymbol);
        for (size_t i = 0; i < productions.size(); ++i) {
            for (const string& symbol : productions[i]) {
                cout << symbol << " ";
            }
            if (i < productions.size() - 1) {
                cout << "| ";
            }
        }
        cout << endl;
    }

    for (const auto& pair : grammar) {
        if (pair.first == startSymbol) continue;
        cout << pair.first << " -> ";
        for (size_t i = 0; i < pair.second.size(); ++i) {
            for (const string& symbol : pair.second[i]) {
                cout << symbol << " ";
            }
            if (i < pair.second.size() - 1) {
                cout << "| ";
            }
        }
        cout << endl;
    }
}

// Function to eliminate direct and indirect left recursion
void eliminateLeftRecursion(Grammar& grammar) {
    vector<string> nonTerminals;
    for (const auto& pair : grammar) {
        nonTerminals.push_back(pair.first);
    }

    for (size_t i = 0; i < nonTerminals.size(); ++i) {
        string Ai = nonTerminals[i];
        
        // 1. Eliminate Indirect Left Recursion
        for (size_t j = 0; j < i; ++j) {
            string Aj = nonTerminals[j];
            vector<Production> newProductionsAi;
            bool replaced = false;
            
            for (const Production& prod : grammar[Ai]) {
                if (!prod.empty() && prod[0] == Aj) {
                    replaced = true;
                    // Replace Ai -> Aj gamma with Ai -> delta1 gamma | delta2 gamma ...
                    for (const Production& prodAj : grammar[Aj]) {
                        Production newProd = prodAj;
                        newProd.insert(newProd.end(), prod.begin() + 1, prod.end());
                        newProductionsAi.push_back(newProd);
                    }
                } else {
                    newProductionsAi.push_back(prod);
                }
            }
            if (replaced) {
                grammar[Ai] = newProductionsAi;
            }
        }

        // 2. Eliminate Direct Left Recursion
        vector<Production> alphas, betas;
        for (const Production& prod : grammar[Ai]) {
            if (!prod.empty() && prod[0] == Ai) {
                alphas.push_back(Production(prod.begin() + 1, prod.end()));
            } else {
                betas.push_back(prod);
            }
        }

        if (!alphas.empty()) { // Has direct left recursion
            string Ai_prime = Ai + "'";
            while (grammar.find(Ai_prime) != grammar.end()) {
                Ai_prime += "'";
            }

            grammar[Ai].clear();
            for (const Production& beta : betas) {
                Production newBeta = beta;
                newBeta.push_back(Ai_prime);
                grammar[Ai].push_back(newBeta);
            }
            // If there were no non-left-recursive productions, add A -> A'
            if (betas.empty()) {
                grammar[Ai].push_back({Ai_prime});
            }

            grammar[Ai_prime].clear();
            for (const Production& alpha : alphas) {
                Production newAlpha = alpha;
                newAlpha.push_back(Ai_prime);
                grammar[Ai_prime].push_back(newAlpha);
            }
            grammar[Ai_prime].push_back({"ep"});
        }
    }
}

// Function to perform Left Factoring
void leftFactor(Grammar& grammar) {
    bool changed = true;
    while (changed) {
        changed = false;
        Grammar newGrammar;
        
        for (auto& pair : grammar) {
            string nonTerminal = pair.first;
            vector<Production>& productions = pair.second;
            
            // Group productions by their first symbol
            map<string, vector<Production>> prefixes;
            for (const Production& prod : productions) {
                if (!prod.empty()) {
                    prefixes[prod[0]].push_back(prod);
                } else {
                    prefixes[""].push_back(prod); // Handle empty production securely
                }
            }
            
            for (auto& prefPair : prefixes) {
                if (prefPair.first == "") {
                    for(auto& p : prefPair.second) newGrammar[nonTerminal].push_back(p);
                    continue;
                }
                
                if (prefPair.second.size() > 1) { // Needs factoring
                    changed = true;
                    
                    // Find longest common prefix
                    vector<string> lcp;
                    size_t minLen = prefPair.second[0].size();
                    for(const auto& p : prefPair.second) {
                        minLen = min(minLen, p.size());
                    }
                    
                    for (size_t i = 0; i < minLen; ++i) {
                        string symbol = prefPair.second[0][i];
                        bool match = true;
                        for (size_t j = 1; j < prefPair.second.size(); ++j) {
                            if (prefPair.second[j][i] != symbol) {
                                match = false;
                                break;
                            }
                        }
                        if (match) {
                            lcp.push_back(symbol);
                        } else {
                            break;
                        }
                    }
                    
                    string newNonTerminal = nonTerminal + "'";
                    while (grammar.find(newNonTerminal) != grammar.end() || newGrammar.find(newNonTerminal) != newGrammar.end()) {
                        newNonTerminal += "'";
                    }
                    
                    Production newProdLCP = lcp;
                    newProdLCP.push_back(newNonTerminal);
                    newGrammar[nonTerminal].push_back(newProdLCP);
                    
                    for (const Production& p : prefPair.second) {
                        Production remainder(p.begin() + lcp.size(), p.end());
                        if (remainder.empty()) {
                            remainder.push_back("ep");
                        }
                        newGrammar[newNonTerminal].push_back(remainder);
                    }
                } else {
                    newGrammar[nonTerminal].push_back(prefPair.second[0]);
                }
            }
        }
        if (changed) {
           grammar = newGrammar;
        }
    }
}

int main() {
    Grammar grammar;
    
    // Initial grammar setup based on your requirements
    // grammar["S"] = {{"(", "L", ")"}, {"a"}};
    // grammar["L"] = {{"L", ",", "S"}, {"S"}};

    // grammar["S"] = {{"a", "S", "S", "b", "S"}, {"a", "S", "a", "S", "b"},{"a", "b", "b"},{"b"}};
    grammar["S"] = {{"a"}, {"a","b"}, {"a","b","c"}, {"a","b","c","d"}};
    
    cout << "Original Grammar:" << endl;
    cout << "---------------------------------" << endl;
    printGrammar(grammar);

    eliminateLeftRecursion(grammar);
    cout << "\nGrammar after Removing Left Recursion:" << endl;
    cout << "---------------------------------" << endl;
    printGrammar(grammar);

    leftFactor(grammar);
    cout << "\nGrammar after Left Factoring:" << endl;
    cout << "---------------------------------" << endl;
    printGrammar(grammar);

    return 0;
}
