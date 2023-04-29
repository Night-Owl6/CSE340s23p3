#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <iostream>
#include <map>
#include <unordered_map>

#include "compiler.h"
#include "lexer.h"

using namespace std;

LexicalAnalyzer lexer;
map<string, int> pos_map;
map<string, int>::iterator it;

struct InstructionNode* parse_body();
struct InstructionNode* helper_stmt();
struct InstructionNode* gram_if_stmt();
struct InstructionNode* gram_for_stmt();
struct InstructionNode* help_stt_lt();
struct InstructionNode* help_in_smt();
struct InstructionNode* while_smt();
struct InstructionNode* out_func();
struct InstructionNode* assi_help_smt();
struct InstructionNode* def_help_s();
struct InstructionNode* parH_case(int b);
struct InstructionNode* help_op(InstructionNode* n);
struct InstructionNode* stch_hel_s(InstructionNode* s);
struct InstructionNode* c_helper(int o, struct InstructionNode* inn);

void v_help_s();
int help_in(const string& s);

// This function takes an instruction node as input and assigns a value to its operand1.
// It reads the next token from the lexer and checks if it is a number.
struct InstructionNode* ao1(InstructionNode* n)
{
    const Token t = lexer.GetToken();

    if (t.token_type == NUM) // If the token is a number
    {
        // Insert the number into the pos_map map with its corresponding index
        // The pos_map map maps the value of the token to its index in the memory array.
        pos_map.insert({ t.lexeme, next_available });

        // Convert the number to an integer and store it in the memory array at the next available index.
        mem[next_available] = stoi(t.lexeme);

        // Increment the next_available index for the next insertion.
        next_available++;
    }

    // Get the index of the token from the memory array.
    const int i = help_in(t.lexeme);

    // Assign the index to operand1 of the instruction node.
    n->assign_inst.operand1_index = i;

    // Return the updated instruction node.
    return n;
}

// This function takes an instruction node as input and assigns a value to its operand2.
// It reads the next token from the lexer and checks if it is a number.
struct InstructionNode* ao2(InstructionNode* n)
{
    const Token t = lexer.GetToken();

    if (t.token_type == NUM) // If the token is a number
    {
        // Insert the number into the pos_map map with its corresponding index.
        // The pos_map map maps the value of the token to its index in the memory array.
        pos_map.insert({ t.lexeme, next_available });

        // Convert the number to an integer and store it in the memory array at the next available index.
        mem[next_available] = stoi(t.lexeme);

        // Increment the next_available index for the next insertion.
        next_available++;
    }

    // Get the index of the token from the memory array.
    const int index = help_in(t.lexeme);

    // Assign the index to operand2 of the instruction node.
    n->assign_inst.operand2_index = index;

    // Return the updated instruction node.
    return n;
}

// This function takes an instruction node as input and assigns a value to its operand1.
// It reads the next token from the lexer and checks if it is a number.
struct InstructionNode* cjo1(InstructionNode* lane)
{
    const Token t = lexer.GetToken();

    if (t.token_type == NUM) // If the token is a number
    {
        // Insert the number into the pos_map map with its corresponding index.
        // The pos_map map maps the value of the token to its index in the memory array.
        pos_map.insert({ t.lexeme, next_available });

        // Convert the number to an integer and store it in the memory array at the next available index.
        mem[next_available] = stoi(t.lexeme);

        // Increment the next_available index for the next insertion.
        next_available++;
    }

    // Get the index of the token from the memory array.
    const int i = help_in(t.lexeme);

    // Assign the index to operand1 of the instruction node.
    lane->cjmp_inst.operand1_index = i;

    // Return the updated instruction node.
    return lane;
}

// This function takes an instruction node as input and assigns a value to its operand2.
// It reads the next token from the lexer and checks if it is a number.
struct InstructionNode* cjo2(InstructionNode* bane)
{
    const Token t = lexer.GetToken();

    if (t.token_type == NUM) // If the token is a number
    {
        // Insert the number into the pos_map map with its corresponding index.
        // The pos_map map maps the value of the token to its index in the memory array.
        pos_map.insert({ t.lexeme, next_available });

        // Convert the number to an integer and store it in the memory array at the next available index.
        mem[next_available] = stoi(t.lexeme);

        // Increment the next_available index for the next insertion.
        next_available++;
    }

    // Get the index of the token from the memory array.
    const int j = help_in(t.lexeme);

    // Assign the index to operand2 of the instruction node.
    bane->cjmp_inst.operand2_index = j;

    // Return the updated instruction node.
    return bane;
}

// This function retrieves the next token from the input stream and checks if its type matches the expected type.
// It takes an expected token type as input and returns the retrieved token if its type matches the expected type.
Token expect(const TokenType expected_type)
{
    // Get the next token from the lexer
    Token stonks = lexer.GetToken();

    // Check if the type of the retrieved token matches the expected type
    if (stonks.token_type != expected_type)
    {  
        // If the types do not match, report a syntax error and exit the program.
        exit(1);
    }

    // If the types match, return the retrieved token.
    return stonks;
}


// Returns the index in memmory corresponding to the given string
int help_in(const string& s)
{
    // Use 'auto' to automatically infer the type of 'it'
    const auto it = pos_map.find(s);

    // If the string is found in the 'pos_map' map, return the corresponding index
    if (it != pos_map.end())
    {
        return it->second;
    }
    // If the string is not found, print an error message and exit the program
    else
    {
        cout << "Not Found" << endl;
        exit(1);
    }
}

// This function is a helper function that parses the first operand of an assignment instruction.
// It takes an instruction node as input, assigns the value of the first operand to it, and returns the updated node.
struct InstructionNode* help_fo(InstructionNode* n)
{
    return n = ao1(n);
}

// This function is a helper function that parses the conditional and second operands of an assignment instruction.
// It takes an instruction node as input, assigns the value of the conditional operand to it,
// assigns the value of the second operand to it, and returns the updated node.
struct InstructionNode* help_so(InstructionNode* h)
{
    h = help_op(h); // Parse the conditional operand
    h = ao2(h); // Parse the second operand
    return h;
}

// This function parses an assignment statement and returns a pointer to the corresponding InstructionNode.
struct InstructionNode* assi_help_smt()
{
    // Check if the next token is an identifier (ID)
    if (lexer.peek(1).token_type != ID)
    {
        return nullptr;
    }

    // Create a new InstructionNode for the assignment statement
    auto c = new InstructionNode;
    c->type = ASSIGN;

    // Get the index of the identifier from the memory array and assign it to the left-hand side of the assignment
    c->assign_inst.left_hand_side_index = help_in(expect(ID).lexeme);

    // Expect an equal sign after the identifier
    expect(EQUAL);

    // Parse the first operand of the assignment statement
    c = help_fo(c);

    // Peek at the next token to see if there's a conditional operator
    const Token semicolon_token = lexer.peek(1);
    if (semicolon_token.token_type != SEMICOLON)
    {
        // If there's a conditional operator, parse the conditional and second operands of the assignment statement
        c = help_so(c);
    }
    else
    {
        // If there's no conditional operator, set the operator to none and the second operand index to null
        c->assign_inst.op = OPERATOR_NONE;
        c->assign_inst.operand2_index = NULL;
    }

    // Expect a semicolon after the assignment statement
    expect(SEMICOLON);

    // Set the next node to nullptr and return the assignment node
    c->next = nullptr;
    return c;
}

// This function takes an instruction node as input and reads the next token from the lexer.
// If the token is a conditional operator, it assigns the corresponding operator or conditional operator to the instruction node.
struct InstructionNode* help_op(InstructionNode* n)
{
    const Token t = lexer.GetToken();

    if (t.token_type == DIV)
    {
        // If the token is a division operator, assign the corresponding operator to the instruction node.
        n->assign_inst.op = OPERATOR_DIV;
    }
    else if (t.token_type == PLUS)
    {
        // If the token is an addition operator, assign the corresponding operator to the instruction node.
        n->assign_inst.op = OPERATOR_PLUS;
    }
    else if (t.token_type == MULT)
    {
        // If the token is a multiplication operator, assign the corresponding operator to the instruction node.
        n->assign_inst.op = OPERATOR_MULT;
    }
    else if (t.token_type == MINUS)
    {
        // If the token is a subtraction operator, assign the corresponding operator to the instruction node.
        n->assign_inst.op = OPERATOR_MINUS;
    }
    else if (t.token_type == GREATER)
    {
        // If the token is a greater than operator, assign the corresponding conditional operator to the instruction node.
        n->cjmp_inst.condition_op = CONDITION_GREATER;
    }
    else if (t.token_type == LESS)
    {
        // If the token is a less than operator, assign the corresponding conditional operator to the instruction node.
        n->cjmp_inst.condition_op = CONDITION_LESS;
    }
    else if (t.token_type == NOTEQUAL)
    {
        // If the token is a not equal operator, assign the corresponding conditional operator to the instruction node.
        n->cjmp_inst.condition_op = CONDITION_NOTEQUAL;
    }

    // Return the updated instruction node.
    return n;
}

// This function appends a new InstructionNode to the end of a linked list of InstructionNodes.
// It takes the head of the list and the node to be appended as inputs.
void append_node(struct InstructionNode* l, struct InstructionNode* j)
{
    // Find the last node in the list
    struct InstructionNode* he = l;
    while (he->next != nullptr)
    {
        he = he->next;
    }

    // Append the new node to the end of the list
    he->next = j;
}

// This function takes a token as input and checks if it is a statement indicator.
// A statement indicator is a token that indicates the beginning of a statement in the input.
bool is_statement_indicator(const Token& tok)
{
    return (tok.token_type == ID || tok.token_type == FOR || tok.token_type == IF ||
        tok.token_type == SWITCH || tok.token_type == WHILE || tok.token_type == OUTPUT ||
        tok.token_type == INPUT);
}

// This function takes a linked list of InstructionNodes as input and parses subsequent statements,
// appending them to the end of the linked list. It returns a pointer to the updated linked list.
struct InstructionNode* next_smt_help(struct InstructionNode* in1)
{
    // Continue parsing while there are statement indicators
    while (true)
    {
        // Peek at the next token to check if it's a statement indicator
        const Token tok = lexer.peek(1);

        // Break the loop if the next token is not a statement indicator
        if (!is_statement_indicator(tok))
        {
            break;
        }

        // Parse the next statement and append it to the linked list
        struct InstructionNode* inst1 = helper_stmt();
        append_node(in1, inst1);
    }

    // Return the updated linked list with the parsed next statements
    return in1;
}

// This function parses a list of statements and returns the first statement in the list.
struct InstructionNode* help_stt_lt()
{
    // Parse the first statement
    struct InstructionNode* in = helper_stmt();

    // Parse subsequent statements if there are any and append them to the linked list
    in = next_smt_help(in);

    // Return the first statement in the list
    return in;
}

// This function creates a start node for the linked list of InstructionNodes.
// The start node is a NOOP (no operation) instruction node that serves as the head of the list.
// The function returns a pointer to the start node.
struct InstructionNode* make_s_node()
{
    // Create a new start node and initialize its type and next pointer
    const auto j = new InstructionNode;
    j->type = NOOP;
    j->next = nullptr;

    // Return a pointer to the start node
    return j;
}

// This function handles the SWITCH case by parsing the switch statement and appending it to the end of the linked list.
// It returns a pointer to the updated linked list.
struct InstructionNode* hand_swi_help(InstructionNode* n)
{
    // Parse the switch statement and append it to the linked list
    InstructionNode* i = stch_hel_s(n);

    // Find the last node in the list and append the start node to it
    InstructionNode* en = i;
    while (en->next != nullptr)
    {
        en = en->next;
    }
    en->next = n;

    // Return a pointer to the updated linked list
    return i;
}

// This function parses a single statement based on the token type.
// It returns a pointer to the InstructionNode for the parsed statement.
InstructionNode* helper_stmt()
{
    // Initialize the InstructionNode pointer to null and create a start node for the linked list
    InstructionNode* i1 = nullptr;
    InstructionNode* start_node = make_s_node();

    // Peek at the next token to determine the type of statement to parse
    const Token t = lexer.peek(1);

    // Parse the statement based on its token type
    if (t.token_type == ID)
    {
        i1 = assi_help_smt();
    }
    else if (t.token_type == INPUT)
    {
        i1 = help_in_smt();
    }
    else if (t.token_type == OUTPUT)
    {
        i1 = out_func();
    }
    else if (t.token_type == IF)
    {
        i1 = gram_if_stmt();
    }
    else if (t.token_type == WHILE)
    {
        i1 = while_smt();
    }
    else if (t.token_type == FOR)
    {
        i1 = gram_for_stmt();
    }
    else if (t.token_type == SWITCH)
    {
        i1 = hand_swi_help(start_node);
    }

    // Return a pointer to the InstructionNode for the parsed statement
    return i1;
}

// This function parses an initialization statement and returns a pointer to the InstructionNode for the parsed statement.
// If the next token is not an ID, it returns a null pointer.
InstructionNode* parse_ini()
{
    // Peek at the next token to check if it's an ID
    const Token t = lexer.peek(1);

    // If the next token is an ID, parse the assignment statement and return its InstructionNode
    // Otherwise, return a null pointer
    return (t.token_type == ID) ? assi_help_smt() : nullptr;
}

// This function parses a conditional statement and returns a pointer to the InstructionNode for the parsed statement.
InstructionNode* pa_con()
{
    // Create a new InstructionNode for the conditional statement and initialize its type
    auto c = new InstructionNode;
    c->type = CJMP;

    // Parse the first operand of the conditional statement and store it in the InstructionNode
    c = cjo1(c);

    // Parse the conditional operator and store it in the InstructionNode
    c = help_op(c);

    // Parse the second operand of the conditional statement and store it in the InstructionNode
    c = cjo2(c);

    // Expect a semicolon after the conditional statement
    expect(SEMICOLON);

    // Return a pointer to the InstructionNode for the parsed statement
    return c;
}

// This function parses an update statement and returns a pointer to the InstructionNode for the parsed statement.
// If the next token is not an ID, it returns a null pointer.
InstructionNode* p_update()
{
    // Peek at the next token to check if it's an ID
    const Token t = lexer.peek(1);

    // If the next token is an ID, parse the assignment statement and return its InstructionNode
    // Otherwise, return a null pointer
    return (t.token_type == ID) ? assi_help_smt() : nullptr;
}

// This function parses a body block and returns a pointer to the InstructionNode for the parsed block.
// If the next token is not a left brace, it returns a null pointer.
InstructionNode* p_body_blk()
{
    // Peek at the next token to check if it's a left brace
    const Token t = lexer.peek(1);

    // If the next token is a left brace, parse the body block and return its InstructionNode
    // Otherwise, return a null pointer
    return (t.token_type == LBRACE) ? parse_body() : nullptr;
}

// This function connects a body node to an update node by appending the update node to the end of the body node's linked list.
void con_body_2_up(InstructionNode* b, InstructionNode* up)
{
    // Find the last node in the body node's linked list
    InstructionNode* ln = b;
    while (ln->next != nullptr)
    {
        ln = ln->next;
    }

    // Append the update node to the end of the body node's linked list
    ln->next = up;
}

// This function creates a jump node with a target InstructionNode and returns a pointer to the jump node.
struct InstructionNode* cre_jNode(InstructionNode* tar)
{
    // Create a new InstructionNode for the jump statement and initialize its type and target
    const auto j = new InstructionNode;
    j->type = JMP;
    j->jmp_inst.target = tar;

    // Return a pointer to the InstructionNode for the jump statement
    return j;
}

// This function creates a NOOP node and returns a pointer to it.
struct InstructionNode* cOP_node1()
{
    // Create a new InstructionNode for the NOOP statement and initialize its type and next to null
    const auto n = new InstructionNode;
    n->type = NOOP;
    n->next = nullptr;

    // Return a pointer to the InstructionNode for the NOOP statement
    return n;
}

// This function connects a jump node and a NOOP node to a condition node by inserting them in the linked list in the correct order.
void con_jOP_n(InstructionNode* j, InstructionNode* n, InstructionNode* c)
{
    // Find the last node in the condition node's linked list
    InstructionNode* end_node = c;
    while (end_node->next != nullptr)
    {
        end_node = end_node->next;
    }

    // Insert the jump node and the NOOP node into the linked list after the condition node
    end_node->next = j;
    j->next = n;

    // Update the target of the condition node to be the NOOP node
    c->cjmp_inst.target = n;
}

struct InstructionNode* gram_for_stmt()
{
    expect(FOR);
    expect(LPAREN);

    // Parse the initialization part of the for loop
    InstructionNode* i = parse_ini();

    // Parse the condition part of the for loop
    InstructionNode* c = pa_con();

    // Parse the update part of the for loop
    InstructionNode* u = p_update();
    expect(RPAREN);

    // Parse the body of the for loop
    InstructionNode* body_node = p_body_blk();

    // Connect the body to the update node
    con_body_2_up(body_node, u);

    // Create a jump node to go back to the condition
    InstructionNode* h = cre_jNode(c);

    // Create a noop node to mark the end of the for loop
    InstructionNode* no = cOP_node1();

    // Connect the jump node to the noop node and set the target of the condition node
    con_jOP_n(h, no, c);

    // Connect the initialization node to the condition node
    i->next = c;

    return i;
}

// Parse an output statement and return the corresponding InstructionNode
struct InstructionNode* out_func()
{
    // Create a new InstructionNode for the output statement
    const auto o = new InstructionNode;

    // Expect the OUTPUT keyword and set the instruction type
    expect(OUTPUT);
    o->type = OUT;

    // Get the variable index and store it in the instruction
    o->output_inst.var_index = help_in(expect(ID).lexeme);

    // Expect a semicolon after the output statement
    expect(SEMICOLON);

    // Set the next node to nullptr and return the output instruction node
    o->next = nullptr;
    return o;
}

// Parse an input statement and return the corresponding InstructionNode
struct InstructionNode* help_in_smt()
{
    // Create a new InstructionNode for the input statement
    const auto in = new InstructionNode;

    // Expect the INPUT keyword and set the instruction type
    expect(INPUT);
    in->type = IN;

    // Get the variable index and store it in the instruction
    in->input_inst.var_index = help_in(expect(ID).lexeme);

    // Expect a semicolon after the input statement
    expect(SEMICOLON);

    // Set the next node to nullptr and return the input instruction node
    in->next = nullptr;
    return in;
}

// This function sets the conditions and operands for the if statement.
void set_conditions_and_operands(InstructionNode* k)
{
    // Parse the first operand for the conditional jump instruction in the if statement
    k = cjo1(k);

    // Parse the conditional operator for the if statement
    k = help_op(k);

    // Parse the second operand for the conditional jump instruction in the if statement
    k = cjo2(k);
}

// This function creates and returns a new NOOP (no operation) node.
struct InstructionNode* cre_noop()
{
    // Allocate memory for the new node
    const auto n = new InstructionNode;

    // Set the type of the node to NOOP
    n->type = NOOP;

    // Set the next pointer of the node to nullptr
    n->next = nullptr;

    // Return the new node
    return n;
}

// This function sets the target of the conditional jump in an if statement to the given target node.
void set_target(InstructionNode* i, InstructionNode* t)
{
    // Find the end node of the if statement's linked list
    InstructionNode* e = i;
    while (e->next != nullptr)
    {
        e = e->next;
    }

    // Append the target node to the end of the linked list
    e->next = t;

    // Set the target of the conditional jump to the target node
    i->cjmp_inst.target = t;
}

// This function parses an 'if' statement and returns an InstructionNode pointer
struct InstructionNode* gram_if_stmt()
{
    // Create a new InstructionNode to represent the 'if' statement
    const auto i = new InstructionNode;

    // Expect the 'IF' keyword to be present
    expect(IF);

    // Assign the 'CJMP' instruction type to the ifStatementNode
    i->type = CJMP;

    // Set the conditions and operands for the 'CJMP' instruction
    set_conditions_and_operands(i);

    // Parse the body of the 'if' statement and assign it to the 'next' node
    i->next = parse_body();

    // Create a NOOP node to mark the end of the 'if' statement
    const auto n = cre_noop();

    // Set the target of the conditional jump to the NOOP node
    set_target(i, n);

    // Return the 'if' statement node
    return i;
}

// This function parses the 'while' keyword
void header_w()
{
    // Expect the 'WHILE' keyword to be present
    expect(WHILE);
}

// This function parses the condition for a 'while' loop
void w_con_help(InstructionNode* w)
{
    // Set the first operand of the 'CJMP' instruction to the current whileNode
    w = cjo1(w);

    // Parse the condition and set it as the operator for the 'CJMP' instruction
    w = help_op(w);

    // Set the second operand of the 'CJMP' instruction to the current whileNode
    w = cjo2(w);
}

// This function parses the body of a 'while' loop
void w_body_help(InstructionNode* w)
{
    // Look ahead one token to check if the body is enclosed in braces
    const Token a = lexer.peek(1);

    // If the body is enclosed in braces, parse it and assign it to the 'next' node of the whileNode
    if (a.token_type == LBRACE)
    {
        w->next = parse_body();
    }
}

// This function creates a loop back to the start of a 'while' loop
void make_loop_b(InstructionNode* w)
{
    // Create a new 'JMP' instruction node
    const auto j = new InstructionNode;

    // Set the type of the instruction to 'JMP'
    j->type = JMP;

    // Set the target of the 'JMP' instruction to the whileNode
    j->jmp_inst.target = w;

    // Create a new NOOP node
    auto* g = new InstructionNode;

    // Set the type of the NOOP node to 'NOOP'
    g->type = NOOP;

    // Set the 'next' node of the NOOP node to null
    g->next = nullptr;

    // Find the last node of the 'while' loop
    InstructionNode* endNode = w;
    while (endNode->next != nullptr)
    {
        endNode = endNode->next;
    }

    // Set the next node of the last node in the 'while' loop to the 'JMP' node
    endNode->next = j;

    // Set the next node of the 'JMP' node to the NOOP node
    j->next = g;

    // Set the target of the 'CJMP' instruction in the whileNode to the NOOP node
    w->cjmp_inst.target = g;
}

// This function parses a 'while' loop statement and returns an InstructionNode pointer
struct InstructionNode* while_smt()
{
    // Create a new InstructionNode to represent the 'while' loop
    const auto j = new InstructionNode;

    // Parse the 'while' keyword
    header_w();

    // Set the instruction type of the whileNode to 'CJMP'
    j->type = CJMP;

    // Parse the condition for the 'while' loop and set the operands for the 'CJMP' instruction
    w_con_help(j);

    // Parse the body of the 'while' loop and set it as the 'next' node of the whileNode
    w_body_help(j);

    // Create a loop back to the start of the 'while' loop
    make_loop_b(j);

    // Return the 'while' loop node
    return j;
}

// This function parses the 'switch' keyword
void swi_head()
{
    // Expect the 'SWITCH' keyword to be present
    expect(SWITCH);
}

// This function parses the expression inside a 'switch' statement and returns its memory index
int expr_swi()
{
    // Expect an 'ID' token to be present and assign it to idToken
    const Token helper = expect(ID);

    // Get the memory index of the ID token and return it
    return help_in(helper.lexeme);
}

// This function finds the last node of a 'switch' statement and returns it
struct InstructionNode* find_swiN(InstructionNode* f)
{
    // Start at the switchNode
    InstructionNode* e = f;

    // Iterate until the next node of the node after the endNode is null
    while (e->next->next != nullptr)
    {
        e = e->next;
    }

    // Return the endNode
    return e;
}

// This function parses either a case list or a default case inside a 'switch' statement
void help_par(InstructionNode* s, int o1, InstructionNode* r)
{
    // Look ahead one token to check if the next case is a 'case' or 'default' keyword
    Token k = lexer.peek(1);

    // If the next keyword is 'case', parse the case list
    if (k.token_type == CASE)
    {
        s = c_helper(o1, r);
        k = lexer.peek(1);
    }

    // If the next keyword is 'default', parse the default case and append it to the end of the switch statement
    if (k.token_type == DEFAULT)
    {
        // Find the end node of the switch statement
        InstructionNode* l = find_swiN(s);

        // Parse the default case and append it to the end of the switch statement
        l->next = def_help_s();
    }
}

// This function parses a 'switch' statement and returns an InstructionNode pointer
struct InstructionNode* stch_hel_s(InstructionNode* s)
{
    // Create a new InstructionNode to represent the 'switch' statement
    const auto sw = new InstructionNode;

    // Parse the 'switch' keyword
    swi_head();

    // Parse the expression inside the 'switch' statement and assign it to switch_operand1
    const int swi_op1 = expr_swi();

    // Expect an opening brace
    expect(LBRACE);

    // Parse either a case list or a default case
    help_par(sw, swi_op1, s);

    // Expect a closing brace
    expect(RBRACE);

    // Return the 'switch' statement node
    return sw;
}

// This is a helper function to connect a JMP node to the input node
void jmp_con_node(const InstructionNode* cn, InstructionNode* i)
{
    // Create a new JMP node and set its target to the input node
    auto* j = new InstructionNode;
    j->type = JMP;
    j->jmp_inst.target = i;

    // Find the end of the target list for the case node and connect it to the JMP node
    InstructionNode* n = cn->cjmp_inst.target;
    while (n->next->next != nullptr)
    {
        n = n->next;
    }
    n->next = j;
}

// This is a helper function to iterate and parse case statements
struct InstructionNode* it_help(InstructionNode* b, int op, InstructionNode* g)
{
    // Look ahead to the next token to check if it is a 'case' keyword
    Token t = lexer.peek(1);

    // Iterate through the list of case statements
    while (t.token_type == CASE)
    {
        // Parse the next case statement in the list
        InstructionNode* n = c_helper(op, g);

        // Find the end of the current case node's target list and connect it to the next case node
        InstructionNode* e = b;
        while (e->next->next != nullptr)
        {
            e = e->next;
        }
        e->next = n;

        // Peek at the next token to check if there are more case statements
        t = lexer.peek(1);
    }

    // Return the case node
    return b;
}

// This function parses a list of 'case' statements and returns an InstructionNode pointer
struct InstructionNode* c_helper(int o, InstructionNode* inn)
{
    // Create an initial case node and set it to nullptr
    InstructionNode* g = nullptr;

    // Peek at the next token to check if it's a 'CASE' keyword
    const Token t = lexer.peek(1);

    // If the next token is 'CASE', parse the first case statement
    if (t.token_type == CASE)
    {
        g = parH_case(o);

        // Connect the JMP node to the input node
        jmp_con_node(g, inn);
    }

    // Iterate through and parse the remaining case statements
    g = it_help(g, o, inn);

    // Return the case node
    return g;
}

// This is a helper function to find the end node of a target list
struct InstructionNode* find_e(InstructionNode* t)
{
    InstructionNode* j = t;

    // Traverse the target list until the end node is reached
    while (j->next != nullptr)
    {
        j = j->next;
    }

    // Return the end node
    return j;
}

// This is a helper function to parse and store a number token in memory
int stor_helpers()
{
    // Expect a 'NUM' token to be present and assign it to t
    Token t = expect(NUM);

    // Insert the number into the memory map and assign it to the next available memory pos_map
    pos_map.insert({ t.lexeme, next_available });
    mem[next_available] = stoi(t.lexeme);
    next_available++;

    // Return the memory index of the number
    return help_in(t.lexeme);
}

// This is a helper function to parse and handle LBRACE token if present
struct InstructionNode* handle_lHelper(InstructionNode* cg)
{
    // Peek at the next token to check if it's a LBRACE
    const Token t = lexer.peek(1);

    // If the next token is LBRACE, parse the body of the case statement
    if (t.token_type == LBRACE)
    {
        cg->cjmp_inst.target = parse_body();
    }

    // Return the case node
    return cg;
}

// This is a helper function to create and connect a NOOP node
struct InstructionNode* cc_help(InstructionNode* c)
{
    // Create a new NOOP node
    const auto n = new InstructionNode;
    n->type = NOOP;
    n->next = nullptr;

    // Find the end node of the current case statement's target list and connect it to the NOOP node
    InstructionNode* g = find_e(c->cjmp_inst.target);
    c->next = n;
    g->next = c->next;

    // Return the case node
    return c;
}

// This function parses a 'case' statement and returns an InstructionNode pointer
struct InstructionNode* parH_case(const int b)
{
    // Create a new case instruction node
    auto m = new InstructionNode;

    // Parse the 'CASE' keyword and set the instruction type and properties
    expect(CASE);
    m->type = CJMP;
    m->cjmp_inst.operand1_index = b;
    m->cjmp_inst.condition_op = CONDITION_NOTEQUAL;

    // Parse the number token and add it to memory
    m->cjmp_inst.operand2_index = stor_helpers();

    // Parse the colon and check if the next token is LBRACE
    expect(COLON);

    // If the next token is LBRACE, parse the body of the case statement
    m = handle_lHelper(m);

    // Create a new NOOP node and set its properties
    // Find the end node of the target list and connect it to the NOOP node
    m = cc_help(m);

    // Return the case instruction node
    return m;
}

// This is a helper function to ensure the next token is 'DEFAULT'
void ensur_def()
{
    // Expect the 'DEFAULT' keyword to be present and assign it to default_token
    const Token def = expect(DEFAULT);

    // If the token type is not 'DEFAULT', throw a runtime error
    if (def.token_type != DEFAULT)
    {
        throw runtime_error("Expected 'DEFAULT' keyword");
    }
}

// This is a helper function to ensure the next token is ':'
void ensur_col()
{
    // Expect a ':' token to be present and assign it to colon_token
    const Token col = expect(COLON);

    // If the token type is not ':', throw a runtime error
    if (col.token_type != COLON)
    {
        throw runtime_error("Expected ':' after 'DEFAULT'");
    }
}

// This is a helper function to handle the LBRACE token and parse the body if present
struct InstructionNode* handle_l_b()
{
    // Peek at the next token to check if it's an LBRACE
    const Token g = lexer.peek(1);

    // If the next token is LBRACE, parse the body of the DEFAULT statement
    InstructionNode* d = nullptr;
    if (g.token_type == LBRACE)
    {
        d = parse_body();
    }

    // Return the default node
    return d;
}

// This function parses a 'default' case and returns an InstructionNode pointer
struct InstructionNode* def_help_s()
{
    // Create a new InstructionNode for the default case

    // Ensure the next token is 'DEFAULT'
    ensur_def();

    // Ensure the next token is ':'
    ensur_col();

    // Check the next token for an opening brace '{' and parse the body if present
    auto* default_node = handle_l_b();

    // Return the default node
    return default_node;
}

// This function parses a body of statements and returns an InstructionNode pointer
struct InstructionNode* parse_body()
{
    // Ensure the next token is an opening brace '{'
    expect(LBRACE);

    // Parse a list of statements inside the body and store the result in 'inst1'
    InstructionNode* inst1 = help_stt_lt();

    // Ensure the next token is a closing brace '}'
    expect(RBRACE);

    // Return the parsed list of statements as an InstructionNode
    return inst1;
}

// This is a helper function to parse the variable section of the program
void helper_va_se()
{
    // Peek at the next token
    const TokenType f = lexer.peek(1).token_type;

    // Check if the next token is an identifier (ID)
    if (f == ID)
    {
        // If it is, parse the variable section
        v_help_s();
    }
}

// This function parses a variable section of the program
void v_help_s()
{
    // Get the current variable token and initialize it in memory
    const Token c = expect(ID);
    mem[next_available] = 0;

    // Insert the variable and its pos_map into the symbol table
    string v = c.lexeme;
    pos_map.insert({ v, next_available });

    // Increment the next available memory pos_map
    next_available++;

    // Peek at the next token
    const TokenType f = lexer.peek(1).token_type;

    // Continue parsing variable declarations or end the section
    if (f != COMMA)
    {

        // If the next token is not a comma, ensure the next token is a semicolon
        expect(SEMICOLON);
    }
    else
    {
        // If the next token is a comma, parse the next variable declaration
        expect(COMMA);
        helper_va_se();
    }
}

// This function generates the intermediate representation of the program
struct InstructionNode* parse_generate_intermediate_representation()
{
    // Parse the variable section of the program
    v_help_s();

    // Parse the body of the program and store the resulting InstructionNode
    struct InstructionNode* stonks = parse_body();

    // Continue processing tokens until the end of the file is reached
    while (lexer.peek(1).token_type != END_OF_FILE)
    {
        // Get the next token as a number, convert it to an integer, and add it to the inputs vector
        int i = stoi(expect(NUM).lexeme);
        inputs.push_back(i);
    }

    // Return the InstructionNode representing the program
    return stonks;
}