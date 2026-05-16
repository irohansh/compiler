#include <bits/stdc++.h>
using namespace std;

struct State
{
    int id;
    map<char, vector<State *>> trans;
    vector<State *> eps;
};

struct NFA
{
    State *start;
    State *accept;
};

int stateCount = 0;

State *newState()
{
    State *s = new State();
    s->id = stateCount++;
    return s;
}

NFA symbolNFA(char c)
{
    State *s = newState();
    State *f = newState();
    s->trans[c].push_back(f);
    return {s, f};
}

NFA concatNFA(NFA a, NFA b)
{
    a.accept->eps.push_back(b.start);
    return {a.start, b.accept};
}

NFA unionNFA(NFA a, NFA b)
{
    State *s = newState();
    State *f = newState();
    s->eps.push_back(a.start);
    s->eps.push_back(b.start);
    a.accept->eps.push_back(f);
    b.accept->eps.push_back(f);
    return {s, f};
}

NFA starNFA(NFA a)
{
    State *s = newState();
    State *f = newState();
    s->eps.push_back(a.start);
    s->eps.push_back(f);
    a.accept->eps.push_back(a.start);
    a.accept->eps.push_back(f);
    return {s, f};
}

int prec(char c)
{
    if (c == '*')
        return 3;
    if (c == '.')
        return 2;
    if (c == '|' || c == '+')
        return 1;
    return 0;
}

bool isSymbol(char c)
{
    return isalnum(c);
}

string formatRegex(string re)
{
    string out;
    for (int i = 0; i < re.size(); i++)
    {
        out += re[i];
        if (i + 1 < re.size())
        {
            if ((isSymbol(re[i]) || re[i] == '*' || re[i] == ')') &&
                (isSymbol(re[i + 1]) || re[i + 1] == '('))
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

NFA buildNFA(string post)
{
    stack<NFA> st;
    for (char c : post)
    {
        if (isSymbol(c))
        {
            st.push(symbolNFA(c));
        }
        else if (c == '*')
        {
            NFA a = st.top();
            st.pop();
            st.push(starNFA(a));
        }
        else
        {
            NFA b = st.top();
            st.pop();
            NFA a = st.top();
            st.pop();
            if (c == '.')
                st.push(concatNFA(a, b));
            else
                st.push(unionNFA(a, b));
        }
    }
    return st.top();
}

void epsilonClosure(State *s, set<State *> &closure)
{
    if (closure.count(s))
        return;
    closure.insert(s);
    for (State *e : s->eps)
        epsilonClosure(e, closure);
}

bool accepts(NFA nfa, string str)
{
    set<State *> curr, next;
    epsilonClosure(nfa.start, curr);

    for (char c : str)
    {
        next.clear();
        for (State *s : curr)
        {
            if (s->trans.count(c))
            {
                for (State *t : s->trans[c])
                    epsilonClosure(t, next);
            }
        }
        curr = next;
    }
    return curr.count(nfa.accept);
}

int main()
{
    string regex;
    cout << "Enter Regular Expression: ";
    cin >> regex;

    regex = formatRegex(regex);
    string postfix = infixToPostfix(regex);
    NFA nfa = buildNFA(postfix);

    cout << "\nE-NFA constructed successfully using Thompson's Construction.\n";

    while (true)
    {
        string input;
        cout << "\nEnter string to verify (type 'exit' to stop): ";
        cin >> input;

        if (input == "exit")
            break;

        if (accepts(nfa, input))
            cout << "Result: ACCEPTED\n";
        else
            cout << "Result: REJECTED\n";
    }

    cout << "\nString verification terminated.\n";
    return 0;
}