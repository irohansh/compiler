#include <cctype>
#include <iomanip>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;

struct Instr {
    string op;
    string arg1;
    string arg2;
    string result;
};

struct Quadruple {
    int index;
    string op;
    string arg1;
    string arg2;
    string result;
};

struct Triple {
    int index;
    string op;
    string arg1;
    string arg2;
};

class TACGen {
public:
    int tempCount = 0;
    int labelCount = 0;
    vector<Instr> code;

    string newTemp() { return "t" + to_string(++tempCount); }
    string newLabel() { return "L" + to_string(++labelCount); }

    void emit(const string &op, const string &a1 = "", const string &a2 = "", const string &res = "") {
        code.push_back({op, a1, a2, res});
    }

    void emitLabel(const string &label) { emit("label", "", "", label); }
    void emitGoto(const string &label) { emit("goto", "", "", label); }
    void emitIfRel(const string &relop, const string &lhs, const string &rhs, const string &label) {
        emit("if" + relop, lhs, rhs, label);
    }
};

enum class TokType { ID, NUM, KW, SYM, END };

struct Token {
    TokType type;
    string text;
};

vector<Token> tokenize(const string &src) {
    vector<Token> out;
    const vector<string> kws = {"if", "else", "while", "for", "break", "return", "int", "void"};
    size_t i = 0;
    while (i < src.size()) {
        if (isspace(static_cast<unsigned char>(src[i]))) {
            ++i;
            continue;
        }

        if (isalpha(static_cast<unsigned char>(src[i])) || src[i] == '_') {
            size_t j = i;
            while (j < src.size() &&
                   (isalnum(static_cast<unsigned char>(src[j])) || src[j] == '_')) {
                ++j;
            }
            string w = src.substr(i, j - i);
            bool isKw = false;
            for (const auto &k : kws) {
                if (w == k) {
                    isKw = true;
                    break;
                }
            }
            out.push_back({isKw ? TokType::KW : TokType::ID, w});
            i = j;
            continue;
        }

        if (isdigit(static_cast<unsigned char>(src[i]))) {
            size_t j = i;
            while (j < src.size() && isdigit(static_cast<unsigned char>(src[j]))) ++j;
            out.push_back({TokType::NUM, src.substr(i, j - i)});
            i = j;
            continue;
        }

        if (i + 1 < src.size()) {
            string two = src.substr(i, 2);
            if (two == "<=" || two == ">=" || two == "==" || two == "!=" || two == "&&" || two == "||") {
                out.push_back({TokType::SYM, two});
                i += 2;
                continue;
            }
        }

        string one(1, src[i]);
        out.push_back({TokType::SYM, one});
        ++i;
    }
    out.push_back({TokType::END, "<end>"});
    return out;
}

struct AExpr {
    enum class Kind { NUM, VAR, BIN, ARR1, ARR2 } kind;
    string val;
    string op;
    unique_ptr<AExpr> left;
    unique_ptr<AExpr> right;
    unique_ptr<AExpr> idx1;
    unique_ptr<AExpr> idx2;
};

struct BExpr {
    enum class Kind { REL, AND, OR } kind;
    string relop;
    unique_ptr<AExpr> lhs;
    unique_ptr<AExpr> rhs;
    unique_ptr<BExpr> left;
    unique_ptr<BExpr> right;
};

struct LValue {
    string name;
    unique_ptr<AExpr> idx1;
    unique_ptr<AExpr> idx2;
};

struct AssignNode {
    LValue lhs;
    unique_ptr<AExpr> rhs;
};

class Parser {
public:
    Parser(const vector<Token> &tokens, TACGen &gen) : t(tokens), g(gen) {}

    void parseProgram() {
        while (!isEnd()) parseStmt();
    }

private:
    const vector<Token> &t;
    TACGen &g;
    size_t p = 0;
    vector<string> breakTargets;

    bool isEnd() const { return t[p].type == TokType::END; }
    const Token &cur() const { return t[p]; }
    const Token &peek(size_t off = 1) const { return t[p + off]; }
    bool match(const string &s) {
        if (cur().text == s) {
            ++p;
            return true;
        }
        return false;
    }
    void expect(const string &s) {
        if (!match(s)) throw runtime_error("Expected '" + s + "', got '" + cur().text + "'");
    }
    string expectId() {
        if (cur().type == TokType::ID) return t[p++].text;
        throw runtime_error("Expected identifier, got '" + cur().text + "'");
    }
    bool isRelop(const string &s) const {
        return s == "<" || s == ">" || s == "<=" || s == ">=" || s == "==" || s == "!=";
    }

    void parseDecl() {
        ++p; // consume 'int' or 'void'
        string id = expectId();
        if (match("(")) {
            g.emitLabel(id);
            while (cur().text != ")") {
                if (cur().text == "int" || cur().text == "void") ++p;
                else if (cur().type == TokType::ID) ++p;
                else if (cur().text == ",") ++p;
                else throw runtime_error("Unexpected token in params: " + cur().text);
            }
            expect(")");
            parseStmt();
        } else {
            while (true) {
                if (match(",")) {
                    expectId();
                } else if (match(";")) {
                    break;
                } else {
                    throw runtime_error("Unexpected token in var decl: " + cur().text);
                }
            }
        }
    }

    void parseReturn() {
        expect("return");
        if (match(";")) {
            g.emit("return", "", "", "");
        } else {
            unique_ptr<AExpr> val = parseAExpr();
            expect(";");
            g.emit("return", genAExpr(val.get()), "", "");
        }
    }

    void parseStmt() {
        if (cur().text == "int" || cur().text == "void") {
            parseDecl();
            return;
        }
        if (cur().text == "return") {
            parseReturn();
            return;
        }
        if (cur().text == "{") {
            parseBlock();
            return;
        }
        if (cur().text == "if") {
            parseIf();
            return;
        }
        if (cur().text == "while") {
            parseWhile();
            return;
        }
        if (cur().text == "for") {
            parseFor();
            return;
        }
        if (cur().text == "break") {
            parseBreak();
            return;
        }
        AssignNode a = parseAssignNode();
        expect(";");
        emitAssign(a);
    }

    void parseBlock() {
        expect("{");
        while (cur().text != "}") parseStmt();
        expect("}");
    }

    void parseIf() {
        expect("if");
        expect("(");
        unique_ptr<BExpr> cond = parseBExpr();
        expect(")");

        string lTrue = g.newLabel();
        string lFalse = g.newLabel();
        string lEnd = g.newLabel();

        genBool(cond.get(), lTrue, lFalse);
        g.emitLabel(lTrue);
        parseStmt();

        if (match("else")) {
            g.emitGoto(lEnd);
            g.emitLabel(lFalse);
            parseStmt();
            g.emitLabel(lEnd);
        } else {
            g.emitLabel(lFalse);
        }
    }

    void parseWhile() {
        expect("while");
        expect("(");
        unique_ptr<BExpr> cond = parseBExpr();
        expect(")");

        string lBegin = g.newLabel();
        string lBody = g.newLabel();
        string lEnd = g.newLabel();

        g.emitLabel(lBegin);
        genBool(cond.get(), lBody, lEnd);
        g.emitLabel(lBody);
        breakTargets.push_back(lEnd);
        parseStmt();
        breakTargets.pop_back();
        g.emitGoto(lBegin);
        g.emitLabel(lEnd);
    }

    void parseFor() {
        expect("for");
        expect("(");
        AssignNode init = parseAssignNode();
        expect(";");
        unique_ptr<BExpr> cond = parseBExpr();
        expect(";");
        AssignNode update = parseAssignNode();
        expect(")");

        emitAssign(init);

        string lBegin = g.newLabel();
        string lBody = g.newLabel();
        string lUpdate = g.newLabel();
        string lEnd = g.newLabel();

        g.emitLabel(lBegin);
        genBool(cond.get(), lBody, lEnd);
        g.emitLabel(lBody);
        breakTargets.push_back(lEnd);
        parseStmt();
        breakTargets.pop_back();
        g.emitLabel(lUpdate);
        emitAssign(update);
        g.emitGoto(lBegin);
        g.emitLabel(lEnd);
    }

    void parseBreak() {
        expect("break");
        expect(";");
        if (breakTargets.empty()) throw runtime_error("break used outside loop");
        g.emitGoto(breakTargets.back());
    }

    AssignNode parseAssignNode() {
        LValue lhs = parseLValue();
        expect("=");
        unique_ptr<AExpr> rhs = parseAExpr();
        return {move(lhs), move(rhs)};
    }

    LValue parseLValue() {
        LValue lv;
        lv.name = expectId();
        if (match("[")) {
            lv.idx1 = parseAExpr();
            expect("]");
            if (match("[")) {
                lv.idx2 = parseAExpr();
                expect("]");
            }
        }
        return lv;
    }

    unique_ptr<BExpr> parseBExpr() { return parseBOr(); }

    unique_ptr<BExpr> parseBOr() {
        unique_ptr<BExpr> node = parseBAnd();
        while (match("||")) {
            auto parent = make_unique<BExpr>();
            parent->kind = BExpr::Kind::OR;
            parent->left = move(node);
            parent->right = parseBAnd();
            node = move(parent);
        }
        return node;
    }

    unique_ptr<BExpr> parseBAnd() {
        unique_ptr<BExpr> node = parseBRel();
        while (match("&&")) {
            auto parent = make_unique<BExpr>();
            parent->kind = BExpr::Kind::AND;
            parent->left = move(node);
            parent->right = parseBRel();
            node = move(parent);
        }
        return node;
    }

    unique_ptr<BExpr> parseBRel() {
        if (match("(")) {
            unique_ptr<BExpr> inside = parseBExpr();
            expect(")");
            return inside;
        }
        unique_ptr<AExpr> lhs = parseAExpr();
        if (!isRelop(cur().text)) throw runtime_error("Expected relational operator, got '" + cur().text + "'");
        string rel = cur().text;
        ++p;
        unique_ptr<AExpr> rhs = parseAExpr();
        auto node = make_unique<BExpr>();
        node->kind = BExpr::Kind::REL;
        node->relop = rel;
        node->lhs = move(lhs);
        node->rhs = move(rhs);
        return node;
    }

    unique_ptr<AExpr> parseAExpr() {
        unique_ptr<AExpr> node = parseATerm();
        while (cur().text == "+" || cur().text == "-") {
            string op = cur().text;
            ++p;
            auto parent = make_unique<AExpr>();
            parent->kind = AExpr::Kind::BIN;
            parent->op = op;
            parent->left = move(node);
            parent->right = parseATerm();
            node = move(parent);
        }
        return node;
    }

    unique_ptr<AExpr> parseATerm() {
        unique_ptr<AExpr> node = parseAFactor();
        while (cur().text == "*" || cur().text == "/") {
            string op = cur().text;
            ++p;
            auto parent = make_unique<AExpr>();
            parent->kind = AExpr::Kind::BIN;
            parent->op = op;
            parent->left = move(node);
            parent->right = parseAFactor();
            node = move(parent);
        }
        return node;
    }

    unique_ptr<AExpr> parseAFactor() {
        if (match("(")) {
            unique_ptr<AExpr> node = parseAExpr();
            expect(")");
            return node;
        }

        if (cur().type == TokType::NUM) {
            auto node = make_unique<AExpr>();
            node->kind = AExpr::Kind::NUM;
            node->val = cur().text;
            ++p;
            return node;
        }

        if (cur().type == TokType::ID) {
            string id = cur().text;
            ++p;
            if (match("[")) {
                auto idx1 = parseAExpr();
                expect("]");
                if (match("[")) {
                    auto idx2 = parseAExpr();
                    expect("]");
                    auto node = make_unique<AExpr>();
                    node->kind = AExpr::Kind::ARR2;
                    node->val = id;
                    node->idx1 = move(idx1);
                    node->idx2 = move(idx2);
                    return node;
                }
                auto node = make_unique<AExpr>();
                node->kind = AExpr::Kind::ARR1;
                node->val = id;
                node->idx1 = move(idx1);
                return node;
            }
            auto node = make_unique<AExpr>();
            node->kind = AExpr::Kind::VAR;
            node->val = id;
            return node;
        }

        throw runtime_error("Unexpected token in arithmetic expression: '" + cur().text + "'");
    }

    string genAExpr(const AExpr *e) {
        if (e->kind == AExpr::Kind::NUM || e->kind == AExpr::Kind::VAR) return e->val;
        if (e->kind == AExpr::Kind::BIN) {
            string l = genAExpr(e->left.get());
            string r = genAExpr(e->right.get());
            string t = g.newTemp();
            g.emit(e->op, l, r, t);
            return t;
        }
        if (e->kind == AExpr::Kind::ARR1) {
            string i1 = genAExpr(e->idx1.get());
            string t = g.newTemp();
            g.emit("load1", e->val, i1, t);
            return t;
        }
        string i1 = genAExpr(e->idx1.get());
        string i2 = genAExpr(e->idx2.get());
        string t = g.newTemp();
        g.emit("load2", e->val, i1 + "," + i2, t);
        return t;
    }

    void emitAssign(const AssignNode &a) {
        string rhs = genAExpr(a.rhs.get());
        if (!a.lhs.idx1) {
            g.emit("=", rhs, "", a.lhs.name);
            return;
        }
        string i1 = genAExpr(a.lhs.idx1.get());
        if (!a.lhs.idx2) {
            g.emit("store1", a.lhs.name, i1, rhs);
            return;
        }
        string i2 = genAExpr(a.lhs.idx2.get());
        g.emit("store2", a.lhs.name, i1 + "," + i2, rhs);
    }

    void genBool(const BExpr *b, const string &lTrue, const string &lFalse) {
        if (b->kind == BExpr::Kind::REL) {
            string x = genAExpr(b->lhs.get());
            string y = genAExpr(b->rhs.get());
            g.emitIfRel(b->relop, x, y, lTrue);
            g.emitGoto(lFalse);
            return;
        }
        if (b->kind == BExpr::Kind::AND) {
            string lMid = g.newLabel();
            genBool(b->left.get(), lMid, lFalse);
            g.emitLabel(lMid);
            genBool(b->right.get(), lTrue, lFalse);
            return;
        }
        string lMid = g.newLabel();
        genBool(b->left.get(), lTrue, lMid);
        g.emitLabel(lMid);
        genBool(b->right.get(), lTrue, lFalse);
    }
};

static void printDivider() {
    cout << "------------------------------------------------------------\n";
}

static void printTAC(const string &title, const vector<Instr> &code) {
    printDivider();
    cout << title << '\n';
    printDivider();
    for (const auto &in : code) {
        if (in.op == "label") {
            cout << in.result << ":\n";
        } else if (in.op == "goto") {
            cout << "goto " << in.result << '\n';
        } else if (in.op.rfind("if", 0) == 0) {
            cout << "if " << in.arg1 << " " << in.op.substr(2) << " " << in.arg2 << " goto " << in.result << '\n';
        } else if (in.op == "return") {
            if (in.arg1.empty()) cout << "return\n";
            else cout << "return " << in.arg1 << '\n';
        } else if (in.op == "=") {
            cout << in.result << " = " << in.arg1 << '\n';
        } else if (in.op == "load1") {
            cout << in.result << " = " << in.arg1 << "[" << in.arg2 << "]\n";
        } else if (in.op == "load2") {
            cout << in.result << " = " << in.arg1 << "[" << in.arg2 << "]\n";
        } else if (in.op == "store1") {
            cout << in.arg1 << "[" << in.arg2 << "] = " << in.result << '\n';
        } else if (in.op == "store2") {
            cout << in.arg1 << "[" << in.arg2 << "] = " << in.result << '\n';
        } else {
            cout << in.result << " = " << in.arg1 << " " << in.op << " " << in.arg2 << '\n';
        }
    }
}

static vector<Quadruple> toQuadruple(const vector<Instr> &code) {
    vector<Quadruple> q;
    for (size_t i = 0; i < code.size(); ++i) {
        q.push_back({static_cast<int>(i + 1), code[i].op, code[i].arg1, code[i].arg2, code[i].result});
    }
    return q;
}

static string remapArg(const string &arg, const unordered_map<string, int> &def) {
    auto it = def.find(arg);
    if (it != def.end()) return "(" + to_string(it->second) + ")";
    return arg;
}

static vector<Triple> toTriple(const vector<Instr> &code) {
    vector<Triple> t;
    unordered_map<string, int> tempDef;
    for (size_t i = 0; i < code.size(); ++i) {
        string a1 = remapArg(code[i].arg1, tempDef);
        string a2 = remapArg(code[i].arg2, tempDef);
        if (code[i].op == "goto") {
            a1 = code[i].result;
            a2 = "";
        } else if (code[i].op == "label") {
            a1 = code[i].result;
            a2 = "";
        } else if (code[i].op.rfind("if", 0) == 0) {
            a2 = a2 + " -> " + code[i].result;
        } else if (code[i].op == "=" || code[i].op == "store1" || code[i].op == "store2") {
            a2 = code[i].result;
        }
        t.push_back({static_cast<int>(i + 1), code[i].op, a1, a2});
        if (!code[i].result.empty() && code[i].result[0] == 't') {
            tempDef[code[i].result] = static_cast<int>(i + 1);
        }
    }
    return t;
}

static void printQuad(const string &title, const vector<Quadruple> &q) {
    printDivider();
    cout << title << '\n';
    printDivider();
    cout << left << setw(6) << "No" << setw(10) << "Op" << setw(14) << "Arg1" << setw(14) << "Arg2"
         << setw(14) << "Result" << '\n';
    for (const auto &x : q) {
        cout << left << setw(6) << x.index << setw(10) << x.op << setw(14) << x.arg1 << setw(14) << x.arg2
             << setw(14) << x.result << '\n';
    }
}

static void printTriple(const string &title, const vector<Triple> &t) {
    printDivider();
    cout << title << '\n';
    printDivider();
    cout << left << setw(6) << "No" << setw(10) << "Op" << setw(18) << "Arg1" << setw(18) << "Arg2" << '\n';
    for (const auto &x : t) {
        cout << left << setw(6) << x.index << setw(10) << x.op << setw(18) << x.arg1 << setw(18) << x.arg2 << '\n';
    }
}

static vector<Instr> generateFromSource(const string &src) {
    TACGen gen;
    vector<Token> tokens = tokenize(src);
    Parser p(tokens, gen);
    p.parseProgram();
    return gen.code;
}

int main() {
    const string srcA = R"(
    void partition(int m, int n)
    {
        int i, j, v, x;
        if (m >= n) return;

        i = m;
        j = n - 1;
        v = a[n];

        while (i <= j) {
            while (i <= j && a[i] <= v)
                i = i + 1;

            while (i <= j && a[j] > v)
                j = j - 1;

            if (i < j) {
                x = a[i];
                a[i] = a[j];
                a[j] = x;
            }
        }

        x = a[i];
        a[i] = a[n];
        a[n] = x;
    }
    )";

    const string srcB = R"(
        if ((a > b && c < d) || (e == f))
            x = a + b;
        else
            x = c - d;
    )";

    const string srcC = R"(
        i = 0;
        found = 0;
        while (i < n) {
            if (A[i] == key) {
                found = 1;
                break;
            }
            i = i + 1;
        }
    )";

    const string srcD = R"(
        for (i = 0; i < m; i = i + 1) {
            for (j = 0; j < n; j = j + 1) {
                if (M[i][j] < 0)
                    M[i][j] = 0;
            }
        }
    )";

    // vector<Instr> a = generateFromSource(srcA);
    vector<Instr> b = generateFromSource(srcB);
    // vector<Instr> c = generateFromSource(srcC);
    // vector<Instr> d = generateFromSource(srcD);

    cout << "Generated TAC\n";
    // printTAC("a) marks processing loop", a);
    printTAC("b) if-then-else scholarship", b);
    // printTAC("c) while loop with break", c);
    // printTAC("d) nested for loops on matrix", d);

    vector<Quadruple> qb = toQuadruple(b);
    vector<Triple> tb = toTriple(b);
    // vector<Quadruple> qc = toQuadruple(c);
    // vector<Triple> tc = toTriple(c);

    printQuad("Quadruple (for b)", qb);
    printTriple("Triple (for b)", tb);
    // printQuad("Quadruple (for c)", qc);
    // printTriple("Triple (for c)", tc);
    return 0;
}
