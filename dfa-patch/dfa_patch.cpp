#include <bits/stdc++.h>
using namespace std;

struct Node
{
    char val;
    Node *left, *right;
    bool nullable;
    set<int> firstpos, lastpos;
    int pos;
    Node(char v) : val(v), left(nullptr), right(nullptr), nullable(false), pos(-1) {}
};

int positionCount = 0;
map<int, set<int>> followpos;
map<int, char> posSymbol;

int prec(char c) {
    if (c == '*') return 3;
    if (c == '.') return 2;
    if (c == '|' || c == '+') return 1;
    return 0;
}

bool isSymbol(char c)
{
    return isalnum(c) || c == '#';
}

string formatRegex(string re)
{
    string out;
    for (int i = 0; i < re.size(); i++)
    {
        char c1 = re[i];
        out += c1;
        if (i + 1 < re.size())
        {
            char c2 = re[i + 1];
            if ((isSymbol(c1) || c1 == '*' || c1 == ')') &&
                (isSymbol(c2) || c2 == '('))
                out += '.';
        }
    }
    return out;
}

string infixToPostfix(string re)
{
    stack<char> st;
    string post;
    for (char c : re)
    {
        if (isSymbol(c))
            post += c;
        else if (c == '(')
            st.push(c);
        else if (c == ')')
        {
            while (!st.empty() && st.top() != '(')
            {
                post += st.top();
                st.pop();
            }
            st.pop();
        }
        else
        {
            while (!st.empty() && prec(st.top()) >= prec(c))
            {
                post += st.top();
                st.pop();
            }
            st.push(c);
        }
    }
    while (!st.empty())
    {
        post += st.top();
        st.pop();
    }
    return post;
}

Node *buildTree(string post)
{
    stack<Node *> st;
    for (char c : post)
    {
        if (isSymbol(c))
        {
            Node *n = new Node(c);
            n->pos = ++positionCount;
            posSymbol[positionCount] = c;
            n->firstpos.insert(n->pos);
            n->lastpos.insert(n->pos);
            st.push(n);
        }
        else if (c == '*')
        {
            Node *a = st.top();
            st.pop();
            Node *n = new Node('*');
            n->left = a;
            n->nullable = true;
            n->firstpos = a->firstpos;
            n->lastpos = a->lastpos;
            for (int i : a->lastpos)
                followpos[i].insert(a->firstpos.begin(), a->firstpos.end());
            st.push(n);
        }
        else
        {
            Node *b = st.top();
            st.pop();
            Node *a = st.top();
            st.pop();
            Node *n = new Node(c);
            n->left = a;
            n->right = b;
            if (c == '|' || c == '+')
            {
                n->nullable = a->nullable || b->nullable;
                n->firstpos = a->firstpos;
                n->firstpos.insert(b->firstpos.begin(), b->firstpos.end());
                n->lastpos = a->lastpos;
                n->lastpos.insert(b->lastpos.begin(), b->lastpos.end());
            }
            else
            {
                n->nullable = a->nullable && b->nullable;
                if (a->nullable)
                {
                    n->firstpos = a->firstpos;
                    n->firstpos.insert(b->firstpos.begin(), b->firstpos.end());
                }
                else
                    n->firstpos = a->firstpos;
                if (b->nullable)
                {
                    n->lastpos = a->lastpos;
                    n->lastpos.insert(b->lastpos.begin(), b->lastpos.end());
                }
                else
                    n->lastpos = b->lastpos;
                for (int i : a->lastpos)
                    followpos[i].insert(b->firstpos.begin(), b->firstpos.end());
            }
            st.push(n);
        }
    }
    return st.top();
}

void printSet(const set<int> &s)
{
    cout << "{ ";
    for (int i : s)
        cout << i << " ";
    cout << "}";
}

void printTreeAttributes(Node *node)
{
    if (node == nullptr)
        return;
    printTreeAttributes(node->left);
    printTreeAttributes(node->right);

    cout << "Symbol: " << node->val;
    if (node->pos != -1)
        cout << " (Pos " << node->pos << ")";
    cout << "\nNullable: " << (node->nullable ? "True" : "False") << "\n";
    cout << "Firstpos: ";
    printSet(node->firstpos);
    cout << "\nLastpos : ";
    printSet(node->lastpos);
    cout << "\n----------------\n";
}

void buildDFA(Node *root)
{
    set<char> inputs;
    for (int i = 1; i <= positionCount; i++) {
        if (posSymbol[i] != '#') {
            inputs.insert(posSymbol[i]);
        }
    }

    vector<set<int>> states;
    map<int, map<char, int>> dfa;
    
    states.push_back(root->firstpos);
    int p = 0;
    while (p < states.size()) {
        set<int> S = states[p];
        for (char c : inputs) {
            set<int> U;
            for (int pos : S) {
                if (posSymbol[pos] == c) {
                    U.insert(followpos[pos].begin(), followpos[pos].end());
                }
            }
            if (!U.empty()) {
                int next_state = -1;
                for (size_t i = 0; i < states.size(); i++) {
                    if (states[i] == U) {
                        next_state = i; break;
                    }
                }
                if (next_state == -1) {
                    next_state = states.size();
                    states.push_back(U);
                }
                dfa[p][c] = next_state;
            }
        }
        p++;
    }

    cout << "\n\nDFA State Table\n";
    cout << "-----------------\n";
    cout << left << setw(30) << "State";
    for (char c : inputs) {
        cout << setw(10) << c;
    }
    cout << "\n";
    
    for (size_t i = 0; i < states.size(); i++) {
        string s_rep = "S" + to_string(i) + " = {";
        bool first = true;
        for (int x : states[i]) {
            if (!first) s_rep += ",";
            s_rep += to_string(x);
            first = false;
        }
        s_rep += "}";
        
        cout << left << setw(30) << s_rep;
        for (char c : inputs) {
            if (dfa[i].count(c)) {
                cout << setw(10) << ("S" + to_string(dfa[i][c]));
            } else {
                cout << setw(10) << "-";
            }
        }
        cout << "\n";
    }
    cout << "\n";
}

int main()
{
    string regex;
    cout << "Enter Regular Expression (end with #): ";
    cin >> regex;

    string formatted = formatRegex(regex);
    string postfix = infixToPostfix(formatted);
    Node *root = buildTree(postfix);

    cout << "\nFormatted Regex : " << formatted;
    cout << "\nPostfix Expression : " << postfix << "\n";

    cout << "\nFollowpos Table\n";
    cout << "----------------\n";
    cout << "Pos\tFollowpos\n";
    for (int i = 1; i <= positionCount; i++)
    {
        cout << i << "\t";
        if (followpos[i].empty())
        {
            cout << "{ }";
        }
        else
        {
            printSet(followpos[i]);
        }
        cout << "\n";
    }

    cout << "\nNode Attributes (Bottom to Root)\n";
    cout << "--------------------------------\n";
    printTreeAttributes(root);

    buildDFA(root);

    return 0;
}