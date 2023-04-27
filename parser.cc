#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <cstdlib>
#include <algorithm>
#include <iostream>
#include <map>

#include "compiler.h"
#include "lexer.h"

using namespace std;

LexicalAnalyzer lexer;
int currInst = 0;
map<string, int> location;
map<string, int>::iterator iter;
struct InstructionNode* completedNode;

struct InstructionNode* parseBody();
struct InstructionNode* parseStmt();
struct InstructionNode* parseIfStmt();
struct InstructionNode* parseForStmt();
struct InstructionNode* parseStmtList();
struct InstructionNode* parseInputStmt();
struct InstructionNode* parseWhileStmt();
struct InstructionNode* parseOutputStmt();
struct InstructionNode* parseAssignStmt();
struct InstructionNode* parseDefaultCase();
struct InstructionNode* parseCase(int op);
struct InstructionNode* conOper(InstructionNode* node);
struct InstructionNode* parseSwitchStmt(InstructionNode* start);
struct InstructionNode* assignOper(InstructionNode* node, int x);
struct InstructionNode* parseCaseList(int op, struct InstructionNode* inNode);

void addToMem(string num) {
    location.insert({num, next_available});
    mem[next_available] = stoi(num);
    next_available++;
}

int memIndex(string str) {
    for (iter = location.begin(); iter != location.end(); ++iter) {
        if (iter->first == str) 
            return iter->second;
    } 
    cout << "Not in mem[]" << endl;
    exit(1);
}

void printMap() {
    if (location.empty()) {
        cout << "Empty map" << endl;
    }
    for (iter = location.begin(); iter != location.end(); ++iter) {
        cout << "[ " << iter->first << " : " << iter->second << " ] ";
    } cout << endl;
}

void syntax_error() {
    cout << "Syntax Error" << endl;
    exit(1);
}

Token expect(TokenType expected_type) {
    Token t = lexer.GetToken();
    if (t.token_type != expected_type) {
        syntax_error();
    } return t;
}

struct InstructionNode* parseAssignStmt() {
    TokenType t = lexer.peek(1).token_type;
    InstructionNode* assignNode = new InstructionNode;
    if (t == ID) {
        assignNode->type = ASSIGN;
        assignNode->assign_inst.left_hand_side_index = memIndex(expect(ID).lexeme);
    }
    t = lexer.GetToken().token_type;
    if (t == EQUAL) {
        assignNode = assignOper(assignNode, 1);
        Token t1 = lexer.peek(1);
        if (t1.token_type != SEMICOLON) {
            assignNode = conOper(assignNode);
            assignNode = assignOper(assignNode, 2);
        } else {
            assignNode->assign_inst.op = OPERATOR_NONE;
            assignNode->assign_inst.operand2_index = NULL;  
        }
    }
    expect(SEMICOLON);
    assignNode->next = nullptr;
    return assignNode;
}

struct InstructionNode* assignOper(InstructionNode* node, int x) {
    Token t = lexer.GetToken();
    if (t.token_type == NUM) {
        addToMem(t.lexeme);
    } int index = memIndex(t.lexeme);
    switch (x) {
        case 1:
            node->assign_inst.operand1_index = index;
            break;
        case 2:
            node->assign_inst.operand2_index = index;
            break;
        case 3:
            node->cjmp_inst.operand1_index = index;
            break;
        case 4:
            node->cjmp_inst.operand2_index = index;
            break;
        default:
            break;
    } return node;
}

struct InstructionNode* conOper(InstructionNode* node) {
    Token t = lexer.GetToken();
    if (t.token_type == PLUS) {
        node->assign_inst.op = OPERATOR_PLUS;
    } else if (t.token_type == MINUS) {
        node->assign_inst.op = OPERATOR_MINUS;
    } else if (t.token_type == MULT) {
        node->assign_inst.op = OPERATOR_MULT;
    } else if (t.token_type == DIV) {
        node->assign_inst.op = OPERATOR_DIV;
    } else if (t.token_type == LESS) {
        node->cjmp_inst.condition_op = CONDITION_LESS;
    } else if (t.token_type == GREATER) {
        node->cjmp_inst.condition_op = CONDITION_GREATER;
    } else if (t.token_type == NOTEQUAL) {
        node->cjmp_inst.condition_op = CONDITION_NOTEQUAL;
    } return node;
}

struct InstructionNode* parseStmtList() {
    struct InstructionNode* inst = nullptr;
    struct InstructionNode* instList = nullptr;
    inst = parseStmt();
    Token t = lexer.peek(1);
    if (t.token_type == ID || t.token_type == FOR || t.token_type == IF || t.token_type == SWITCH || 
        t.token_type == WHILE || t.token_type == OUTPUT || t.token_type == INPUT) {
        instList = parseStmtList();
        struct InstructionNode* endNode = inst;
        while (endNode->next != nullptr) {
            endNode = endNode->next;
        }
        endNode->next = instList;
    }
    return inst;
}

struct InstructionNode* parseStmt() {
    struct InstructionNode* inst = nullptr;
    struct InstructionNode* startNode = new InstructionNode;
    struct InstructionNode* endNode;
    startNode->type = NOOP;
    startNode->next = nullptr;
    Token t = lexer.peek(1);
    switch (t.token_type) {
        case ID:
            inst = parseAssignStmt();
            break;
        case INPUT:
            inst = parseInputStmt();
            break;
        case OUTPUT:
            inst = parseOutputStmt();
            break;
        case IF:
            inst = parseIfStmt();
            break;
        case WHILE:
            inst = parseWhileStmt();
            break;
        case FOR:
            inst = parseForStmt();
            break;
        case SWITCH:
            inst = parseSwitchStmt(startNode);
            endNode = inst;
            while (endNode->next != nullptr) {
                endNode = endNode->next;
            } endNode->next = startNode;
            break;
        default:
            break;
    } return inst;
}

struct InstructionNode* parseForStmt() {
    struct InstructionNode* forInst = new InstructionNode;
    struct InstructionNode* assignStmt = new InstructionNode;
    expect(FOR);
    expect(LPAREN);

    Token t = lexer.peek(1);
    if (t.token_type == ID) {
        forInst = parseAssignStmt();
    } 
    struct InstructionNode* whileStmt = new InstructionNode;
    whileStmt->type = CJMP;
    whileStmt = assignOper(whileStmt, 3);
    whileStmt = conOper(whileStmt);
    whileStmt = assignOper(whileStmt, 4);

    expect(SEMICOLON);
    t = lexer.peek(1);
    if (t.token_type == ID) {
        assignStmt = parseAssignStmt();
        assignStmt->next = nullptr;
        expect(RPAREN);
    }
    t = lexer.peek(1);
    if (t.token_type == LBRACE) {
        whileStmt->next = parseBody();
    } 
    struct InstructionNode* addStmt = whileStmt->next;
    while (addStmt->next != nullptr) {
        addStmt = addStmt->next;
    } addStmt->next = assignStmt;

    struct InstructionNode* jmp = new InstructionNode;
    jmp->type = JMP;
    jmp->jmp_inst.target = whileStmt;

    struct InstructionNode* noop = new InstructionNode;
    noop->type = NOOP;
    noop->next = nullptr;
    jmp->next = noop;

    struct InstructionNode* endNode = whileStmt;
    while (endNode->next != nullptr) {
        endNode = endNode->next;
    }
    endNode->next = jmp;
    whileStmt->cjmp_inst.target = noop;
    forInst->next = whileStmt;

    return forInst;
}

struct InstructionNode* parseOutputStmt() {
    struct InstructionNode* inst = new InstructionNode;
    expect(OUTPUT);
    inst->type = OUT;
    inst->output_inst.var_index = memIndex(expect(ID).lexeme);
    expect(SEMICOLON);
    inst->next = nullptr;
    return inst;
}

struct InstructionNode* parseInputStmt() {
    struct InstructionNode* inst = new InstructionNode;
    expect(INPUT);
    inst->type = IN;
    inst->input_inst.var_index = memIndex(expect(ID).lexeme);
    expect(SEMICOLON);
    inst->next = nullptr;
    return inst;
}

struct InstructionNode* parseIfStmt() {
    struct InstructionNode* instNode = new InstructionNode;
    expect(IF);
    instNode->type = CJMP;
    instNode = assignOper(instNode, 3);
    instNode = conOper(instNode);
    instNode = assignOper(instNode, 4);
    instNode->next = parseBody();

    struct InstructionNode* noOpNode = new InstructionNode;
    noOpNode->type = NOOP;
    noOpNode->next = nullptr;

    struct InstructionNode* endNode = instNode;
    while (endNode->next != nullptr) {
        endNode = endNode->next;
    }
    endNode->next = noOpNode;
    instNode->cjmp_inst.target = noOpNode;

    return instNode;
}

struct InstructionNode* parseWhileStmt() {
    struct InstructionNode* whileInst = new InstructionNode;
    expect(WHILE);
    whileInst->type = CJMP;
    whileInst = assignOper(whileInst, 3);
    whileInst = conOper(whileInst);
    whileInst = assignOper(whileInst, 4);

    Token t = lexer.peek(1);
    if (t.token_type == LBRACE) {
        whileInst->next = parseBody();
    }
    struct InstructionNode* jmpNode = new InstructionNode;
    jmpNode->type = JMP;
    jmpNode->jmp_inst.target = whileInst;

    struct InstructionNode* noOpNode = new InstructionNode;
    noOpNode->type = NOOP;
    noOpNode->next = nullptr;

    struct InstructionNode* endNode = whileInst;
    while (endNode->next != nullptr) {
        endNode = endNode->next;
    }
    endNode->next = jmpNode;
    jmpNode->next = noOpNode;
    whileInst->cjmp_inst.target = noOpNode;
    return whileInst;
}

struct InstructionNode* parseSwitchStmt(InstructionNode* start) {
    struct InstructionNode* switchInst = new InstructionNode;
    expect(SWITCH);
    Token t = expect(ID);
    int switchOp1 = memIndex(t.lexeme);
    expect(LBRACE);

    t = lexer.peek(1);
    if (t.token_type == CASE) {
        switchInst = parseCaseList(switchOp1, start);
    }
    t = lexer.peek(1);
    if (t.token_type == DEFAULT) {
        struct InstructionNode* endNode = switchInst;
        while (endNode->next->next != nullptr) {
            endNode = endNode->next;
        }
        endNode->next = parseDefaultCase();
        expect(RBRACE);
    } else if (t.token_type == RBRACE) {
        expect(RBRACE);
        return switchInst;
    }
    return switchInst;
}

struct InstructionNode* parseCaseList(int op, struct InstructionNode* inNode) {
    struct InstructionNode* caseNode = new InstructionNode;
    struct InstructionNode* caseList = nullptr;
    Token t = lexer.peek(1);
    if (t.token_type == CASE) {
        caseNode = parseCase(op);

        struct InstructionNode* jmp = new InstructionNode;
        jmp->type = JMP;
        jmp->jmp_inst.target = inNode;
        struct InstructionNode* endNode = caseNode->cjmp_inst.target;
        while (endNode->next->next != nullptr) {
            endNode = endNode->next;
        }
        endNode->next = jmp;
    }
    t = lexer.peek(1);
    if (t.token_type == CASE) {
        caseList = parseCaseList(op, inNode);
        struct InstructionNode* endNode = caseNode;
        while (endNode->next->next != nullptr) {
            endNode = endNode->next;
        }
        endNode->next = caseList;
    }
    return caseNode;
}

struct InstructionNode* parseCase(int op) {
    struct InstructionNode* caseInst = new InstructionNode;
    expect(CASE);
    caseInst->type = CJMP;
    caseInst->cjmp_inst.operand1_index = op;
    caseInst->cjmp_inst.condition_op = CONDITION_NOTEQUAL;
    
    Token t = expect(NUM);
    addToMem(t.lexeme);
    caseInst->cjmp_inst.operand2_index = memIndex(t.lexeme);

    expect(COLON);
    t = lexer.peek(1);
    if (t.token_type == LBRACE) {
        caseInst->cjmp_inst.target = parseBody();
    }
    struct InstructionNode* noOpNode = new InstructionNode;
    noOpNode->type = NOOP;
    noOpNode->next = nullptr;

    struct InstructionNode* endNode = caseInst->cjmp_inst.target;
    while (endNode->next != nullptr) {
        endNode = endNode->next;
    }
    caseInst->next = noOpNode;
    endNode->next = caseInst->next;
    return caseInst;
}

struct InstructionNode* parseDefaultCase() {
    struct InstructionNode* defaultNode = new InstructionNode;
    expect(DEFAULT);
    expect(COLON);
    Token t = lexer.peek(1);
    if (t.token_type == LBRACE) {
        defaultNode = parseBody();
    }
    return defaultNode;
}

void parseNumList() {
    TokenType t1 = lexer.peek(1).token_type;
    while (t1 != END_OF_FILE) {
        inputs.push_back(stoi(expect(NUM).lexeme));
        t1 = lexer.peek(1).token_type;
    }
}

struct InstructionNode* parseBody() {
    struct InstructionNode* body = nullptr;
    expect(LBRACE);
    body = parseStmtList();
    expect(RBRACE);
    return body;
}

void parseVarSec() {
    TokenType t1 = lexer.peek(1).token_type;
    TokenType t2 = lexer.peek(2).token_type;
    if (t1 == ID) {
        Token currVar = expect(ID);
        mem[next_available] = 0;
        string lex = currVar.lexeme;
        location.insert({lex, next_available});
        next_available++;
        if (t2 == COMMA) {
            expect(COMMA);
            parseVarSec();
        } else {
            expect(SEMICOLON);
        }
    }
}

struct InstructionNode* parse_generate_intermediate_representation() {
    parseVarSec();
    completedNode = parseBody();
    parseNumList();
    return completedNode;
}