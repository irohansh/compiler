#include <bits/stdc++.h>

using namespace std;

struct Quad{
    string op,arg1,arg2,res;
};

struct Triple{
    string op,arg1,arg2;
};

// DAG Node
struct DAGNode {
    int id;
    string label;
    int left;
    int right;
    string computed_val;
};

vector<DAGNode> dag;
map<string, int> varToNode;
map<tuple<string, int, int>, int> exprToNode;
vector<string> dagOutput;

string trim(const string& str) {
    size_t first = str.find_first_not_of(' ');
    if (string::npos == first) return "";
    size_t last = str.find_last_not_of(' ');
    return str.substr(first, (last - first + 1));
}

int getLeafNode(const string& var) {
    if (varToNode.count(var)) {
        return varToNode[var];
    }
    int id = dag.size();
    dag.push_back({id, var, -1, -1, var});
    varToNode[var] = id;
    return id;
}

int getOpNode(const string& op, int left_id, int right_id, const string& arg1, const string& arg2) {
    auto key = make_tuple(op, left_id, right_id);
    if (exprToNode.count(key)) {
        return exprToNode[key];
    }
    int id = dag.size();
    dag.push_back({id, op, left_id, right_id, ""});
    exprToNode[key] = id;
    
    // Store requested horizontal format to be printed at the end
    if (op == "uminus") {
        dagOutput.push_back("minus left : " + trim(arg1));
    } else {
        dagOutput.push_back(op + " left : " + trim(arg1) + " , right : " + trim(arg2));
    }
    
    return id;
}

int precedence(string op) {
    if(op=="||") return 1;
    if(op=="&&") return 2;
    if(op=="<" || op==">" || op=="==" || op=="!=") return 3;
    if(op=="+" || op=="-") return 4;
    if(op=="*" || op=="/" || op=="%") return 5;
    if(op=="^") return 6;
    if(op=="uminus") return 7;
    return 0; // for parentheses and default
}

bool isOperatorToken(string s) {
    return (s=="+" || s=="-" || s=="*" || s=="/" || s=="%" || s=="^" ||
            s=="||" || s=="&&" || s=="==" || s=="!=" || s=="<" || s==">" || s=="uminus");
}

vector<string> tokenize(string s) {
    vector<string> tokens;
    string cur = "";
    for(int i=0; i<s.size(); i++){
        if(isspace(s[i])) continue;
        if(s[i]=='&' && i+1<s.size() && s[i+1]=='&') {
            if(cur!="") tokens.push_back(cur); cur="";
            tokens.push_back("&&"); i++;
        }
        else if(s[i]=='|' && i+1<s.size() && s[i+1]=='|') {
            if(cur!="") tokens.push_back(cur); cur="";
            tokens.push_back("||"); i++;
        }
        else if(s[i]=='=' || s[i]=='(' || s[i]==')' || s[i]=='+' || s[i]=='-' || s[i]=='*' || s[i]=='/' || s[i]=='^') {
            if(cur!="") tokens.push_back(cur); cur="";
            tokens.push_back(string(1, s[i]));
        } else {
            cur += s[i];
        }
    }
    if(cur!="") tokens.push_back(cur);
    return tokens;
}

int main(){

    vector<string> inputs = {
        // "x = (a + b) * (a + b) + (a + b) * c + c * (a + b)"

        // "x = ((a+b*c) ^ (d*e))+(f*g)-(d*e)"
        
        // "x = a + b",
        // "y = x + c",
        // "z = a + b",
        // "p = z + c",
        // "q = y + p"

        "a=b*-c+b*-c"

        // "a[i] = b* c - b*d"
    };

    cout << "----- MULTILINE INPUT -----\n";
    for(const string& line : inputs) {
        cout << line << "\n";
    }

    vector<string> tac;
    vector<Quad> quad;
    vector<Triple> triple;
    map<string, int> tempToTripleIdx;
    
    int temp_count = 1;

    for(int i = 0; i < inputs.size(); i++){
        vector<string> tokens = tokenize(inputs[i]);
        if(tokens.size() < 3 || tokens[1] != "=") continue;

        string lhs = tokens[0];
        vector<string> expr(tokens.begin() + 2, tokens.end());

        stack<string> values;
        stack<string> ops;

        auto reduceTop = [&]() {
            string op = ops.top(); ops.pop();
            
            if (op == "uminus") {
                string a = values.top(); values.pop();
                
                int left_id = getLeafNode(a);
                auto key = make_tuple(op, left_id, -1);
                
                if (exprToNode.count(key)) {
                    int node_id = exprToNode[key];
                    string existing_var = dag[node_id].computed_val;
                    values.push(existing_var);
                    return; 
                }
                
                string tempVar = "t" + to_string(temp_count++);
                tac.push_back(tempVar + " = minus " + a);
                quad.push_back({"uminus", a, "-", tempVar});
                triple.push_back({"uminus", a, ""});
                tempToTripleIdx[tempVar] = triple.size() - 1;
                
                int node_id = getOpNode(op, left_id, -1, a, "");
                dag[node_id].computed_val = tempVar;
                varToNode[tempVar] = node_id;
                values.push(tempVar);
                return;
            }

            string b = values.top(); values.pop();
            string a = values.top(); values.pop();

            int left_id = getLeafNode(a);
            int right_id = getLeafNode(b);
            auto key = make_tuple(op, left_id, right_id);

            // COMMON SUBEXPRESSION ELIMINATION (DAG OPTIMIZATION)
            if (exprToNode.count(key)) {
                int node_id = exprToNode[key];
                string existing_var = dag[node_id].computed_val;
                values.push(existing_var);
                return; // TAC Optimization bypassed
            }

            string tempVar = "t" + to_string(temp_count++);

            tac.push_back(tempVar + " = " + a + " " + op + " " + b);
            quad.push_back({op, a, b, tempVar});
            triple.push_back({op, a, b});
            tempToTripleIdx[tempVar] = triple.size() - 1;
            
            // Generate DAG mapped structurally
            int node_id = getOpNode(op, left_id, right_id, a, b);
            dag[node_id].computed_val = tempVar;
            varToNode[tempVar] = node_id;

            values.push(tempVar);
        };

        for(int j=0; j<expr.size(); j++){
            string token = expr[j];

            if(token == "-") {
                if(j == 0 || expr[j-1] == "(" || isOperatorToken(expr[j-1])) {
                    token = "uminus";
                }
            }

            if(token == "("){
                ops.push(token);
            }
            else if(token == ")"){
                while(!ops.empty() && ops.top() != "("){
                    reduceTop();
                }
                if(!ops.empty() && ops.top() == "(") ops.pop();
            }
            else if(isOperatorToken(token)){
                while(!ops.empty() && ops.top() != "(" && precedence(ops.top()) >= precedence(token)){
                    reduceTop();
                }
                ops.push(token);
            }
            else {
                values.push(token);
            }
        }

        while(!ops.empty()){
            reduceTop();
        }

        string finalRes = values.top(); values.pop();
        
        tac.push_back(lhs + " = " + finalRes);
        quad.push_back({"=", finalRes, "-", lhs});
        triple.push_back({"=", lhs, finalRes});
        
        // Connect the LHS var to the final resolved DAG node
        int final_id = getLeafNode(finalRes);
        varToNode[lhs] = final_id;
    }

    cout << "\n----- THREE ADDRESS CODE -----\n";
    for(auto &x : tac) cout << x << endl;

    cout << "\n----- QUADRUPLE -----\n";
    cout << left << setw(10) << "Op"
         << setw(10) << "Arg1"
         << setw(10) << "Arg2"
         << setw(10) << "Result" << endl;

    for(auto &q : quad) {
        cout << setw(10) << q.op
             << setw(10) << q.arg1
             << setw(10) << q.arg2
             << setw(10) << q.res
             << endl;
    }

    cout << "\n----- TRIPLE -----\n";
    cout << left << setw(10) << "Index"
         << setw(10) << "Op"
         << setw(10) << "Arg1"
         << setw(10) << "Arg2" << endl;

    for(int i = 0; i < triple.size(); i++){
        string a1 = triple[i].arg1;
        string a2 = triple[i].arg2;
        if(tempToTripleIdx.count(a1)) a1 = "(" + to_string(tempToTripleIdx[a1]) + ")";
        if(tempToTripleIdx.count(a2)) a2 = "(" + to_string(tempToTripleIdx[a2]) + ")";

        cout << left << setw(10) << "(" + to_string(i) + ")"
             << setw(10) << triple[i].op
             << setw(10) << a1
             << setw(10) << a2
             << endl;
    }

    cout << "\n----- INDIRECT TRIPLE -----\n";
    cout << "\nPointer Table\n";
    for(int i = 0; i < triple.size(); i++){
        cout << "P" << i << " -> (" << i << ")" << endl;
    }

    cout << "\nTriple Table\n";
    cout << left << setw(10) << "Index"
         << setw(10) << "Op"
         << setw(10) << "Arg1"
         << setw(10) << "Arg2" << endl;

    for(int i = 0; i < triple.size(); i++){
        string a1 = triple[i].arg1;
        string a2 = triple[i].arg2;
        if(tempToTripleIdx.count(a1)) a1 = "(" + to_string(tempToTripleIdx[a1]) + ")";
        if(tempToTripleIdx.count(a2)) a2 = "(" + to_string(tempToTripleIdx[a2]) + ")";

        cout << left << setw(10) << "(" + to_string(i) + ")"
             << setw(10) << triple[i].op
             << setw(10) << a1
             << setw(10) << a2
             << endl;
    }

    cout << "\n----- CONSTRUCTING DAG -----\n";
    for(const string& line : dagOutput) cout << line << endl;

    return 0;
}
