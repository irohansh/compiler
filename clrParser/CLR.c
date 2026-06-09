#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdbool.h>

#define MAX_PRODS 100
#define MAX_SYM 50
#define MAX_SYM_LEN 32
#define MAX_ITEMS 2000
#define MAX_STATES 500
#define MAX_RHS_LEN 20

typedef struct {
    char lhs[MAX_SYM_LEN];
    char rhs[MAX_RHS_LEN][MAX_SYM_LEN];
    int rhs_count;
} Production;

typedef struct {
    int prodNo;
    int dotPos;
    char lookahead[MAX_SYM_LEN];
} Item;

typedef struct {
    Item items[MAX_ITEMS];
    int num_items;
} State;

typedef struct {
    char lhs[MAX_SYM_LEN];
    char rhs[MAX_PRODS][MAX_RHS_LEN][MAX_SYM_LEN];
    int rhs_count[MAX_PRODS];
    int num_rules;
} GrammarEntry;

GrammarEntry raw_grammar[MAX_SYM];
int num_raw_nt = 0;

Production prods[MAX_PRODS];
int num_prods = 0;

char ordered_nt[MAX_SYM][MAX_SYM_LEN];
int num_ordered_nt = 0;

char ordered_t[MAX_SYM][MAX_SYM_LEN];
int num_ordered_t = 0;

char FIRST[MAX_SYM][MAX_SYM][MAX_SYM_LEN];
int num_first[MAX_SYM];

char FOLLOW[MAX_SYM][MAX_SYM][MAX_SYM_LEN];
int num_follow[MAX_SYM];

State states[MAX_STATES];
int num_states = 0;

char ACTION[MAX_STATES][MAX_SYM][16];
int GOTO_TABLE[MAX_STATES][MAX_SYM];

int is_ordered_nt(const char* sym) {
    for (int i = 0; i < num_ordered_nt; ++i) {
        if (strcmp(ordered_nt[i], sym) == 0) return i;
    }
    return -1;
}

int is_ordered_t(const char* sym) {
    for (int i = 0; i < num_ordered_t; ++i) {
        if (strcmp(ordered_t[i], sym) == 0) return i;
    }
    return -1;
}

int has_grammar(const char* sym) {
    for (int i = 0; i < num_raw_nt; i++) {
        if (strcmp(raw_grammar[i].lhs, sym) == 0) return i;
    }
    return -1;
}

int set_insert(char set[][MAX_SYM_LEN], int* size, const char* val) {
    for(int i=0; i<*size; i++) {
        if(strcmp(set[i], val) == 0) return 0;
    }
    strcpy(set[(*size)++], val);
    return 1;
}

int set_contains(char set[][MAX_SYM_LEN], int size, const char* val) {
    for(int i=0; i<size; i++) {
        if(strcmp(set[i], val) == 0) return 1;
    }
    return 0;
}

void add_grammar(const char* lhs, ...) {
    int idx = has_grammar(lhs);
    if (idx == -1) {
        idx = num_raw_nt++;
        strcpy(raw_grammar[idx].lhs, lhs);
        raw_grammar[idx].num_rules = 0;
    }
    int r = raw_grammar[idx].num_rules++;
    raw_grammar[idx].rhs_count[r] = 0;
    
    va_list args;
    va_start(args, lhs);
    const char* sym;
    while ((sym = va_arg(args, const char*)) != NULL) {
        strcpy(raw_grammar[idx].rhs[r][raw_grammar[idx].rhs_count[r]++], sym);
    }
    va_end(args);
}

void loadGrammar(const char* start_symbol) {
    char augmented_start[MAX_SYM_LEN];
    strcpy(augmented_start, start_symbol);
    strcat(augmented_start, "'");
    
    strcpy(prods[0].lhs, augmented_start);
    strcpy(prods[0].rhs[0], start_symbol);
    prods[0].rhs_count = 1;
    num_prods++;
    
    strcpy(ordered_nt[num_ordered_nt++], augmented_start);
    strcpy(ordered_nt[num_ordered_nt++], start_symbol);
    
    char order[MAX_SYM][MAX_SYM_LEN];
    int num_order = 0;
    strcpy(order[num_order++], start_symbol);
    
    char visited_nt[MAX_SYM][MAX_SYM_LEN];
    int num_visited_nt = 0;
    set_insert(visited_nt, &num_visited_nt, start_symbol);
    
    char visited_t[MAX_SYM][MAX_SYM_LEN];
    int num_visited_t = 0;
    
    for (int i = 0; i < num_order; ++i) {
        char curr[MAX_SYM_LEN];
        strcpy(curr, order[i]);
        
        int g_idx = has_grammar(curr);
        if (g_idx != -1) {
            for (int j = 0; j < raw_grammar[g_idx].num_rules; ++j) {
                strcpy(prods[num_prods].lhs, curr);
                prods[num_prods].rhs_count = 0;
                
                for (int k = 0; k < raw_grammar[g_idx].rhs_count[j]; ++k) {
                    char symbol[MAX_SYM_LEN];
                    strcpy(symbol, raw_grammar[g_idx].rhs[j][k]);
                    strcpy(prods[num_prods].rhs[prods[num_prods].rhs_count++], symbol);
                    
                    if (strcmp(symbol, "ep") != 0) {
                        if (has_grammar(symbol) != -1) {
                            if (set_insert(visited_nt, &num_visited_nt, symbol)) {
                                strcpy(order[num_order++], symbol);
                                strcpy(ordered_nt[num_ordered_nt++], symbol);
                            }
                        } else {
                            if (set_insert(visited_t, &num_visited_t, symbol)) {
                                strcpy(ordered_t[num_ordered_t++], symbol);
                            }
                        }
                    }
                }
                num_prods++;
            }
        }
    }
    strcpy(ordered_t[num_ordered_t++], "$");
}

int get_nt_idx(const char* nt) {
    return is_ordered_nt(nt);
}

void addFirst(int nt_idx, const char* terminal, int* changed) {
    if (set_insert(FIRST[nt_idx], &num_first[nt_idx], terminal)) *changed = 1;
}

void computeFIRST() {
    for (int i = 0; i < num_ordered_nt; ++i) num_first[i] = 0;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int p = 0; p < num_prods; ++p) {
            int lhs_idx = get_nt_idx(prods[p].lhs);
            if (prods[p].rhs_count == 0 || (prods[p].rhs_count == 1 && strcmp(prods[p].rhs[0], "ep") == 0)) {
                addFirst(lhs_idx, "ep", &changed);
                continue;
            }
            int all_have_epsilon = 1;
            for (int i = 0; i < prods[p].rhs_count; ++i) {
                char symbol[MAX_SYM_LEN];
                strcpy(symbol, prods[p].rhs[i]);
                int sym_nt_idx = get_nt_idx(symbol);
                if (sym_nt_idx == -1) {
                    if (strcmp(symbol, "ep") != 0) addFirst(lhs_idx, symbol, &changed);
                    all_have_epsilon = 0;
                    break;
                } else {
                    for (int f = 0; f < num_first[sym_nt_idx]; ++f) {
                        if (strcmp(FIRST[sym_nt_idx][f], "ep") != 0) {
                            addFirst(lhs_idx, FIRST[sym_nt_idx][f], &changed);
                        }
                    }
                    if (!set_contains(FIRST[sym_nt_idx], num_first[sym_nt_idx], "ep")) {
                        all_have_epsilon = 0;
                        break;
                    }
                }
            }
            if (all_have_epsilon) addFirst(lhs_idx, "ep", &changed);
        }
    }
}

void addFollow(int nt_idx, const char* terminal, int* changed) {
    if (set_insert(FOLLOW[nt_idx], &num_follow[nt_idx], terminal)) *changed = 1;
}

void computeFOLLOW() {
    for (int i = 0; i < num_ordered_nt; ++i) num_follow[i] = 0;
    int changed = 1;
    int e_prime_idx = get_nt_idx(prods[0].lhs);
    int e_idx = get_nt_idx(prods[1].lhs);
    addFollow(e_prime_idx, "$", &changed);
    addFollow(e_idx, "$", &changed);
    while (changed) {
        changed = 0;
        for (int p = 0; p < num_prods; ++p) {
            for (int i = 0; i < prods[p].rhs_count; ++i) {
                char B[MAX_SYM_LEN];
                strcpy(B, prods[p].rhs[i]);
                int B_idx = get_nt_idx(B);
                if (B_idx == -1) continue;
                int all_next_have_epsilon = 1;
                for (int j = i + 1; j < prods[p].rhs_count; ++j) {
                    char next_symbol[MAX_SYM_LEN];
                    strcpy(next_symbol, prods[p].rhs[j]);
                    int next_idx = get_nt_idx(next_symbol);
                    if (next_idx == -1) {
                        if (strcmp(next_symbol, "ep") != 0) addFollow(B_idx, next_symbol, &changed);
                        all_next_have_epsilon = 0;
                        break;
                    } else {
                        for (int f = 0; f < num_first[next_idx]; ++f) {
                            if (strcmp(FIRST[next_idx][f], "ep") != 0) {
                                addFollow(B_idx, FIRST[next_idx][f], &changed);
                            }
                        }
                        if (!set_contains(FIRST[next_idx], num_first[next_idx], "ep")) {
                            all_next_have_epsilon = 0;
                            break;
                        }
                    }
                }
                if (all_next_have_epsilon) {
                    int lhs_idx = get_nt_idx(prods[p].lhs);
                    for (int f = 0; f < num_follow[lhs_idx]; ++f) addFollow(B_idx, FOLLOW[lhs_idx][f], &changed);
                }
            }
        }
    }
}

int item_eq(Item a, Item b) {
    return a.prodNo == b.prodNo && a.dotPos == b.dotPos && strcmp(a.lookahead, b.lookahead) == 0;
}

int state_insert_item(State* s, Item item) {
    for (int i = 0; i < s->num_items; ++i) {
        if (item_eq(s->items[i], item)) return 0;
    }
    int insert_pos = s->num_items;
    while (insert_pos > 0) {
        Item prev = s->items[insert_pos - 1];
        if (prev.prodNo > item.prodNo || 
           (prev.prodNo == item.prodNo && prev.dotPos > item.dotPos) ||
           (prev.prodNo == item.prodNo && prev.dotPos == item.dotPos && strcmp(prev.lookahead, item.lookahead) > 0)) {
            s->items[insert_pos] = s->items[insert_pos - 1];
            insert_pos--;
        } else {
            break;
        }
    }
    s->items[insert_pos] = item;
    s->num_items++;
    return 1;
}

int state_eq(State a, State b) {
    if (a.num_items != b.num_items) return 0;
    for (int i = 0; i < a.num_items; ++i) {
        if (!item_eq(a.items[i], b.items[i])) return 0;
    }
    return 1;
}

int get_first_of_string(char sequence[][MAX_SYM_LEN], int count, char result[][MAX_SYM_LEN], int* res_count) {
    *res_count = 0;
    int all_have_ep = 1;
    for (int i = 0; i < count; ++i) {
        char* symbol = sequence[i];
        int sym_idx = is_ordered_nt(symbol);
        if (sym_idx == -1) {
            if (strcmp(symbol, "ep") != 0) {
                set_insert(result, res_count, symbol);
            }
            all_have_ep = 0;
            break;
        } else {
            for (int f = 0; f < num_first[sym_idx]; ++f) {
                if (strcmp(FIRST[sym_idx][f], "ep") != 0) {
                    set_insert(result, res_count, FIRST[sym_idx][f]);
                }
            }
            if (!set_contains(FIRST[sym_idx], num_first[sym_idx], "ep")) {
                all_have_ep = 0;
                break;
            }
        }
    }
    if (all_have_ep) set_insert(result, res_count, "ep");
    return 1;
}

void closure(State* state) {
    int changed = 1;
    while (changed) {
        changed = 0;
        int initial_items = state->num_items;
        for (int i = 0; i < initial_items; ++i) {
            Item item = state->items[i];
            int p = item.prodNo;
            if (item.dotPos < prods[p].rhs_count) {
                char B[MAX_SYM_LEN];
                strcpy(B, prods[p].rhs[item.dotPos]);
                if (strcmp(B, "ep") != 0 && is_ordered_nt(B) != -1) {
                    char sequence[MAX_RHS_LEN + 1][MAX_SYM_LEN];
                    int seq_count = 0;
                    for (int k = item.dotPos + 1; k < prods[p].rhs_count; ++k) {
                        strcpy(sequence[seq_count++], prods[p].rhs[k]);
                    }
                    strcpy(sequence[seq_count++], item.lookahead);
                    
                    char first_res[MAX_SYM][MAX_SYM_LEN];
                    int num_first_res = 0;
                    get_first_of_string(sequence, seq_count, first_res, &num_first_res);
                    
                    for (int j = 0; j < num_prods; ++j) {
                        if (strcmp(prods[j].lhs, B) == 0) {
                            for (int f = 0; f < num_first_res; ++f) {
                                Item new_item;
                                new_item.prodNo = j;
                                new_item.dotPos = 0;
                                strcpy(new_item.lookahead, first_res[f]);
                                if (state_insert_item(state, new_item)) {
                                    changed = 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

State gotoState(State state, const char* X) {
    State next_state;
    next_state.num_items = 0;
    for (int i = 0; i < state.num_items; ++i) {
        Item item = state.items[i];
        if (item.dotPos < prods[item.prodNo].rhs_count) {
            char symbol[MAX_SYM_LEN];
            strcpy(symbol, prods[item.prodNo].rhs[item.dotPos]);
            if (strcmp(symbol, X) == 0) {
                Item next_item;
                next_item.prodNo = item.prodNo;
                next_item.dotPos = item.dotPos + 1;
                strcpy(next_item.lookahead, item.lookahead);
                state_insert_item(&next_state, next_item);
            }
        }
    }
    closure(&next_state);
    return next_state;
}

void buildCanonical() {
    State start;
    start.num_items = 0;
    Item start_item;
    start_item.prodNo = 0;
    start_item.dotPos = 0;
    strcpy(start_item.lookahead, "$");
    state_insert_item(&start, start_item);
    closure(&start);
    states[num_states++] = start;
    
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < num_states; ++i) {
            char symbols[MAX_SYM*2][MAX_SYM_LEN];
            int num_symbols = 0;
            for (int j = 0; j < num_ordered_nt; ++j) strcpy(symbols[num_symbols++], ordered_nt[j]);
            for (int j = 0; j < num_ordered_t; ++j) strcpy(symbols[num_symbols++], ordered_t[j]);
            
            for (int k = 0; k < num_symbols; ++k) {
                char X[MAX_SYM_LEN];
                strcpy(X, symbols[k]);
                if (strcmp(X, "ep") == 0 || strcmp(X, "$") == 0) continue;
                State next_state = gotoState(states[i], X);
                if (next_state.num_items == 0) continue;
                int found = 0;
                for (int s = 0; s < num_states; ++s) {
                    if (state_eq(states[s], next_state)) { found = 1; break; }
                }
                if (!found) {
                    states[num_states++] = next_state;
                    changed = 1;
                }
            }
        }
    }
}

void buildCLR() {
    for (int i = 0; i < num_states; ++i) {
        for (int t = 0; t < num_ordered_t; ++t) strcpy(ACTION[i][t], "");
        for (int nt = 0; nt < num_ordered_nt; ++nt) GOTO_TABLE[i][nt] = -1;
        
        for (int k = 0; k < states[i].num_items; ++k) {
            Item item = states[i].items[k];
            int p = item.prodNo;
            int is_ep = (prods[p].rhs_count == 1 && strcmp(prods[p].rhs[0], "ep") == 0);
            
            if (!is_ep && item.dotPos < prods[p].rhs_count) {
                char a[MAX_SYM_LEN];
                strcpy(a, prods[p].rhs[item.dotPos]);
                State next_state = gotoState(states[i], a);
                int j = -1;
                for (int s = 0; s < num_states; ++s) {
                    if (state_eq(states[s], next_state)) { j = s; break; }
                }
                if (j != -1) {
                    int a_nt = is_ordered_nt(a);
                    if (a_nt == -1) {
                        int a_t = is_ordered_t(a);
                        if (a_t != -1) {
                            if (strlen(ACTION[i][a_t]) == 0 || ACTION[i][a_t][0] == 's') {
                                sprintf(ACTION[i][a_t], "s%d", j);
                            }
                        }
                    } else {
                        GOTO_TABLE[i][a_nt] = j;
                    }
                }
            } else {
                if (p == 0) {
                    if (strcmp(item.lookahead, "$") == 0) {
                        int idx_dollar = is_ordered_t("$");
                        strcpy(ACTION[i][idx_dollar], "acc");
                    }
                } else {
                    int fol_idx = is_ordered_t(item.lookahead);
                    if (fol_idx != -1) {
                        if (strlen(ACTION[i][fol_idx]) == 0 || ACTION[i][fol_idx][0] == 'r') {
                            sprintf(ACTION[i][fol_idx], "r%d", p);
                        }
                    }
                }
            }
        }
    }
}

void formatSet(char dest[], char set[][MAX_SYM_LEN], int size) {
    strcpy(dest, "{");
    for (int i = 0; i < size; ++i) {
        if (i > 0) strcat(dest, ",");
        strcat(dest, set[i]);
    }
    strcat(dest, "}");
}

void printFirstFollow() {
    printf("=== FIRST and FOLLOW Sets ===\n\n");
    int w_nt = -15;
    int w_set = -20;
    
    printf("%*s | %*s | %s\n", w_nt, "Nonterminal", w_set, "FIRST", "FOLLOW");
    for(int i=0; i<15; i++) printf("-"); printf("-+-");
    for(int i=0; i<20; i++) printf("-"); printf("-+-");
    for(int i=0; i<20; i++) printf("-"); printf("\n");
    
    for (int i = 0; i < num_ordered_nt; ++i) {
        char fst[256], fol[256];
        formatSet(fst, FIRST[i], num_first[i]);
        formatSet(fol, FOLLOW[i], num_follow[i]);
        printf("%*s | %*s | %s\n", w_nt, ordered_nt[i], w_set, fst, fol);
    }
    printf("\n");
}

void printParsingTable() {
    int cell_w = -4;
    printf("=== Parsing Table ===\n\n");
    
    int action_w = num_ordered_t * 4 + num_ordered_t - 1;
    int goto_w = num_ordered_nt * 4 + num_ordered_nt - 1;
    
    printf("%-8s | %-*s | %s\n", "State", action_w, "ACTION", "GOTO");
    for(int i=0; i<8; i++) printf("-"); printf("-+-");
    for(int i=0; i<action_w; i++) printf("-"); printf("-+-");
    for(int i=0; i<goto_w; i++) printf("-"); printf("\n");
    
    printf("%8s | ", "");
    for (int i = 0; i < num_ordered_t; ++i) {
        printf("%*s", cell_w, ordered_t[i]);
        if (i + 1 < num_ordered_t) printf(" ");
    }
    printf(" | ");
    for (int i = 0; i < num_ordered_nt; ++i) {
        printf("%*s", cell_w, ordered_nt[i]);
        if (i + 1 < num_ordered_nt) printf(" ");
    }
    printf("\n");
    
    for(int i=0; i<8; i++) printf("-"); printf("-+-");
    for(int i=0; i<action_w; i++) printf("-"); printf("-+-");
    for(int i=0; i<goto_w; i++) printf("-"); printf("\n");
    
    for (int i = 0; i < num_states; ++i) {
        printf("%-8d | ", i);
        for (int j = 0; j < num_ordered_t; ++j) {
            printf("%*s", cell_w, ACTION[i][j]);
            if (j + 1 < num_ordered_t) printf(" ");
        }
        printf(" | ");
        for (int j = 0; j < num_ordered_nt; ++j) {
            char val[16] = "";
            if (GOTO_TABLE[i][j] != -1) sprintf(val, "%d", GOTO_TABLE[i][j]);
            printf("%*s", cell_w, val);
            if (j + 1 < num_ordered_nt) printf(" ");
        }
        printf("\n");
    }
    printf("\n");
}

void parse(const char* input_tokens[], int in_size) {
    int state_stack[MAX_ITEMS];
    char symbol_stack[MAX_ITEMS][MAX_SYM_LEN];
    int top = 0;
    
    state_stack[top] = 0;
    int ip = 0;
    int step = 1;
    
    int W_STEP_C = -5;
    int W_STACK_C = -35;
    int W_INPUT_C = -25;
    int W_ACTION_C = -10;
    
    printf("=== Parsing Trace ===\n\n");
    printf("%*s | %*s | %*s | %s\n", W_STEP_C, "Step", W_STACK_C, "Stack", W_INPUT_C, "Input", "Action");
    for(int i=0;i<5;i++)printf("-");printf("-+-");
    for(int i=0;i<35;i++)printf("-");printf("-+-");
    for(int i=0;i<25;i++)printf("-");printf("-+-");
    for(int i=0;i<10;i++)printf("-");printf("\n");
    
    while (1) {
        int state = state_stack[top];
        const char* a = input_tokens[ip];
        
        char inpBuf[256] = "";
        for (int i = ip; i < in_size; ++i) {
            strcat(inpBuf, input_tokens[i]);
            strcat(inpBuf, " ");
        }
        
        char stackBuf[512] = "";
        sprintf(stackBuf, "%d", state_stack[0]);
        for (int i = 0; i < top; ++i) {
            char temp[64];
            sprintf(temp, " %s %d", symbol_stack[i], state_stack[i + 1]);
            strcat(stackBuf, temp);
        }
        
        int a_idx = is_ordered_t(a);
        char act[16] = "";
        if (a_idx != -1) strcpy(act, ACTION[state][a_idx]);
        
        char step_str[16];
        sprintf(step_str, "%d", step++);
        
        if (strlen(act) == 0) {
            printf("%*s | %*s | %*s | %s\n", W_STEP_C, step_str, W_STACK_C, stackBuf, W_INPUT_C, inpBuf, "ERROR");
            break;
        } else if (act[0] == 's') {
            int next_state = atoi(act + 1);
            printf("%*s | %*s | %*s | %s\n", W_STEP_C, step_str, W_STACK_C, stackBuf, W_INPUT_C, inpBuf, act);
            strcpy(symbol_stack[top], a);
            state_stack[++top] = next_state;
            ip++;
        } else if (act[0] == 'r') {
            int p = atoi(act + 1);
            printf("%*s | %*s | %*s | %s\n", W_STEP_C, step_str, W_STACK_C, stackBuf, W_INPUT_C, inpBuf, act);
            int rlen = prods[p].rhs_count;
            int is_epsilon = (rlen == 1 && strcmp(prods[p].rhs[0], "ep") == 0);
            if (is_epsilon) rlen = 0;
            top -= rlen;
            int top_state = state_stack[top];
            int lhs_nt = is_ordered_nt(prods[p].lhs);
            int gt = GOTO_TABLE[top_state][lhs_nt];
            
            char intStack[512];
            strcpy(intStack, stackBuf);
            sprintf(intStack, "%d", state_stack[0]);
            for (int i = 0; i < top; ++i) {
                char temp[64];
                sprintf(temp, " %s %d", symbol_stack[i], state_stack[i + 1]);
                strcat(intStack, temp);
            }
            strcat(intStack, " ");
            strcat(intStack, prods[p].lhs);
            
            char gt_str[16];
            sprintf(gt_str, "%d", gt);
            
            char step2_str[16];
            sprintf(step2_str, "%d", step++);
            
            printf("%*s | %*s | %*s | %s\n", W_STEP_C, step2_str, W_STACK_C, intStack, W_INPUT_C, inpBuf, gt_str);
            strcpy(symbol_stack[top], prods[p].lhs);
            state_stack[++top] = gt;
        } else if (strcmp(act, "acc") == 0) {
            printf("%*s | %*s | %*s | %s\n", W_STEP_C, step_str, W_STACK_C, stackBuf, W_INPUT_C, inpBuf, "acc");
            break;
        }
    }
}

int main() {

    add_grammar("S", "C", "C", NULL);

    add_grammar("C", "c", "C", NULL);
    add_grammar("C", "d", NULL);
    
    loadGrammar("S");
    
    printf("=== Augmented Grammar ===\n");
    for (int i = 0; i < num_prods; ++i) {
        printf("  %d. %s -> ", i, prods[i].lhs);
        for (int j = 0; j < prods[i].rhs_count; ++j) {
            printf("%s ", prods[i].rhs[j]);
        }
        printf("\n");
    }
    
    computeFIRST();
    computeFOLLOW();
    printFirstFollow();
    buildCanonical();
    buildCLR();
    
    printParsingTable();
    
    const char* input[] = {"c", "d", "d", "$"};
    int in_size = sizeof(input) / sizeof(input[0]);
    parse(input, in_size);
    
    return 0;
}
