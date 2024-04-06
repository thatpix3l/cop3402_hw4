// Written by:
// Jonathan Alonso
// Kerem Aydin

#include <ctype.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const int iden_size = 11;  // max characters for identifier
const int number_size = 5; // max characters for number
const int ar_min = 3;      // min activation record size
const int assembly_size = 3;

// Lexical analysis token kind
typedef enum token_kind {
  oddsym = 0,
  identsym,
  numbersym,
  plussym,
  minussym,
  multsym,
  slashsym,
  fisym,
  eqsym,
  neqsym,
  lessym,
  leqsym,
  gtrsym,
  geqsym,
  lparentsym,
  rparentsym,
  commasym,
  semicolonsym,
  periodsym,
  becomessym,
  beginsym,
  endsym,
  ifsym,
  thensym,
  whilesym,
  dosym,
  constsym,
  varsym,
  writesym,
  readsym,
  // modsym,
  callsym,
  proceduresym
} token_kind;

char *op_codes[] = {"",    "LIT", "OPR", "LOD", "STO",
                    "CAL", "INC", "JMP", "JPC", "SYS"};
const int op_codes_size = sizeof(op_codes) / sizeof(op_codes[0]);

char *sys_subcodes[] = {"", "OUT", "INP", "EOP"};
const int sys_subcodes_size = sizeof(sys_subcodes) / sizeof(sys_subcodes[0]);

char *opr_subcodes[] = {"RTN", "ADD", "SUB", "MUL", "DIV", "EQL",
                        "NEQ", "LSS", "LEQ", "GTR", "GEQ", "ODD"};
const int opr_subcodes_size = sizeof(opr_subcodes) / sizeof(opr_subcodes[0]);

// Syntax analysis symbol kind.
typedef enum symbol_kind { constant = 1, variable, procedure } symbol_kind;

#define check(ptr)                                                             \
  if (!ptr || ptr->stored == 0)                                                \
  return NULL

// Peek top of list
#define new_peek(kind)                                                         \
  kind *peek_##kind(kind##_list *list) {                                       \
    check(list);                                                               \
                                                                               \
    return &list->arr[list->stored - 1];                                       \
  }

// Pop top of list
#define new_pop(kind)                                                          \
  kind *pop_##kind(kind##_list *list) {                                        \
    check(list);                                                               \
                                                                               \
    kind *top = peek_##kind(list);                                             \
    if (top) {                                                                 \
      kind empty;                                                              \
      list->arr[list->stored - 1] = empty;                                     \
      list->stored--;                                                          \
    }                                                                          \
    return top;                                                                \
  }

// Custom list type
#define new_list_type(kind)                                                    \
  typedef struct kind##_list {                                                 \
    kind *arr;                                                                 \
    int stored;                                                                \
    int alloc;                                                                 \
  } kind##_list;                                                               \
  new_peek(kind);                                                              \
  new_pop(kind)

#define init_list(ptr)                                                         \
  ptr->arr = NULL;                                                             \
  ptr->stored = 0;                                                             \
  ptr->alloc = 0

void list_realloc_err() {
  printf("something went wrong reallocating a list, exiting...\n");
  exit(4);
}

// Make room in list for adding new items
#define new_alloc(kind)                                                        \
  void alloc_##kind(kind##_list *list) {                                       \
    if (0 <= list->stored && list->stored < list->alloc)                       \
      return;                                                                  \
                                                                               \
    list->alloc = (list->alloc) == 0 ? 1 : list->alloc * 2;                    \
    list->arr = realloc(list->arr, list->alloc * sizeof(kind));                \
                                                                               \
    if (list->arr == NULL)                                                     \
      list_realloc_err();                                                      \
  }

// Push item to list
#define new_push(kind, pre, post)                                              \
  void push_##kind(kind##_list *list, kind item) {                             \
    alloc_##kind(list);                                                        \
    pre(list);                                                                 \
    list->arr[list->stored] = item;                                            \
    list->stored++;                                                            \
    post(list);                                                                \
  }

#define new_list_manager(kind, pre_push, post_push)                            \
  new_alloc(kind);                                                             \
  new_push(kind, pre_push, post_push);

// Callback that works for any list; does nothing.
void ignore(void *v) {}

// Create a list for string management, that also accounts for null characters.
new_list_type(char);

// Ensure top of char list is not NULL terminator
void char_pre_push(char_list *l) {

  // If no item in list or top item is not null, return.
  char *c = peek_char(l);
  if (!c || *c != '\0')
    return;

  // Decrement stored count so current push overwrites null
  l->stored--;
}

// Terminate end of char list
void char_post_push(char_list *l) {
  l->arr[l->stored] = '\0';
  l->stored++;
}
new_list_manager(char, char_pre_push, char_post_push);

// Token generated from PL/0 source code.
typedef struct token {
  token_kind kind;  // token kind
  char_list lexeme; // lexeme string used to detect type of token
  int row;          // input source line row start
  int col;          // input source line column start
} token;
new_list_type(token);
new_list_manager(token, ignore, ignore);

// Assembly emitted from pl/0 source code.
typedef struct assembly {
  char *pretty;
  int op;
  int l;
  int m;
} assembly;
new_list_type(assembly);
new_list_manager(assembly, ignore, ignore);

// Symbol reference
typedef struct symbol {
  symbol_kind kind; // symbol kind
  char_list name;   // name used to reference symbol
  int level;        // lex level
  int m;            // how far off from activation record this is located
  int const_val;    // constant literal from code
} symbol;
new_list_type(symbol);
new_list_manager(symbol, ignore, ignore);

#define delim "([^a-zA-Z])"                   // don't match letters
#define uncom(reg) .uncompiled = "(^" reg ")" // match begin of line

// Regex wrapper; used for organization.
typedef struct rg {
  char *uncompiled; // uncompiled regex
  regex_t compiled; // compiled regex
} rg;

// Lexemes
rg lex_rg_list[] = {
    {uncom("odd") delim},                 // oddsym
    {uncom("[a-zA-Z]([a-zA-Z]|[0-9])*")}, // identsym
    {uncom("[0-9]([0-9])*")},             // numbersym
    {uncom("\\+")},                       // plussym
    {uncom("\\-")},                       // minussym
    {uncom("\\*")},                       // multsym
    {uncom("\\/")},                       // slashsym
    {uncom("fi") delim},                  // fisym
    {uncom("=")},                         // eqsym
    {uncom("\\<>")},                      // neqsym
    {uncom("<")},                         // lessym
    {uncom("<=")},                        // leqsym
    {uncom(">")},                         // gtrsym
    {uncom(">=")},                        // geqsym
    {uncom("\\(")},                       // lparentsym
    {uncom("\\)")},                       // rparentsym
    {uncom(",")},                         // commasym
    {uncom(";")},                         // semicolonsym
    {uncom("\\.")},                       // periodsym
    {uncom(":=")},                        // becomessym
    {uncom("begin") delim},               // beginsym
    {uncom("end") delim},                 // endsym
    {uncom("if") delim},                  // ifsym
    {uncom("then") delim},                // thensym
    {uncom("while") delim},               // whilesym
    {uncom("do") delim},                  // dosym
    {uncom("const") delim},               // constsym
    {uncom("var") delim},                 // varsym
    {uncom("write") delim},               // writesym
    {uncom("read") delim},                // readsym
    // {uncom("mod") delim},                 // modsym
    {uncom("call") delim},     // callsym
    {uncom("procedure") delim} // proceduresym
};
#define DEFINED_LEXEMES sizeof(lex_rg_list) / sizeof(lex_rg_list[0])

// Regex to match a string starting with a comment.
rg comment_rg = {uncom("/\\*(.|\r|\n|\t|\v)*\\*/")};

char_list input; // in-memory copy of PL/0 input

token_list tokens;  // lexical tokens
int lex_err_count;  // lexical error count
int lex_level = -1; // lexical level

symbol_list symbols;

// Parse lexeme using specific regex.
token *parse_lexeme_specific(char *s, int reg_idx) {

  regmatch_t submatches[2];                           // submatches
  regex_t *compiled = &lex_rg_list[reg_idx].compiled; // compiled regex

  // If can't match regex, exit early
  if (regexec(compiled, s, 2, submatches, 0))
    return NULL;

  // Only here if regex matches

  token *t = malloc(sizeof(token)); // malloc token
  t->kind = reg_idx;                // regex used to match
  init_list((&t->lexeme));

  int match_length = submatches[1].rm_eo;

  // Store copy of name of regex
  for (int i = 0; i < match_length; i++) {
    char c = s[i];
    push_char(&t->lexeme, c);
  }

  return t;
}

// Parse lexeme using all regexes, starting with non-identifier regex.
token *parse_lexeme(char *s) {

  token *t;

  // For each lexeme regex...
  for (int reg_idx = 0; reg_idx < DEFINED_LEXEMES; ++reg_idx) {

    // Skip if identifier regex
    if (reg_idx == identsym)
      continue;

    // Return if non-identifier regex works
    t = parse_lexeme_specific(s, reg_idx);
    if (t)
      return t;
  }

  // Otherwise, try to run using identifier regex
  return parse_lexeme_specific(s, identsym);
}

int code_idx = -1;
assembly_list asm_list;

void fix_jpc_jmp(int idx) {
  asm_list.arr[idx].m = (code_idx + 1) * assembly_size;
}

// In an array of strings, find and return matching index's string.
char *find_string(int matching_idx, char **string_array, int array_size,
                  int array_start) {
  for (int i = array_start; i < array_size; i++) {
    if (matching_idx == i)
      return string_array[i];
  }
  return NULL;
}

int emit(int op_code, int level, int m) {
  code_idx++;

  assembly a;
  a.op = op_code;
  a.l = level;
  a.m = m;

  // If SYS, find pretty subcode name.
  if (a.op == 9)
    a.pretty = find_string(a.m, sys_subcodes, sys_subcodes_size, 1);

  // Else if OPR, find pretty subcode name.
  else if (a.op == 2)
    a.pretty = find_string(a.m, opr_subcodes, opr_subcodes_size, 0);

  // Else, fall back to whatever name for regular op code.
  else
    a.pretty = find_string(a.op, op_codes, op_codes_size, 0);

  push_assembly(&asm_list, a);
  return asm_list.stored - 1;
}

// Check if given string starts with a comment
int is_comment(char *s) {
  regmatch_t comment_submatch[1];
  int err = regexec(&comment_rg.compiled, s, 1, comment_submatch, 0);
  if (err) {
    return 0;
  }
  return comment_submatch[0].rm_eo;
}

token *latest_token; // latest valid token retrieved before error
int tokens_idx = -1; // lexical token index

// Print message and panic.
void err(char *s) {

  token *t = latest_token;
  if (!t) {
    printf("line: 1, column: 1, error: %s\n", s);
    return;
  }

  printf("line: %d, column: %d, lexeme: %s, regex: %s, error: %s\n", t->row + 1,
         t->col + t->lexeme.stored, t->lexeme.arr,
         lex_rg_list[t->kind].uncompiled, s);
  exit(2);
}

token *next_token(token_kind token_sym, char *msg) {

  token *t;     // optional or required token, depending on msg
  tokens_idx++; // increment to next token

  // Get token if accessible
  if (0 <= tokens_idx && tokens_idx < tokens.stored) {
    t = &tokens.arr[tokens_idx];
    latest_token = t;
  }

  // If cannot get more tokens or does not match...
  if (!t || t->kind != token_sym) {

    // ...and also required, error
    if (msg) {
      err(msg);
    }

    // Rollback token index for next use
    tokens_idx--;

    return NULL;
  }

  return t;
}

void is_expression();

symbol *find_symbol(char *str) {

  for (int i = symbols.stored - 1; i >= 0; i--) {

    symbol *s = &symbols.arr[i];

    if (strcmp(str, s->name.arr) == 0)
      return s;
  }

  return NULL;
}

void is_factor() {
  token *t;
  t = next_token(identsym, NULL);
  if (t) {

    symbol *s = find_symbol(t->lexeme.arr);

    if (!s || s->kind == procedure) {
      err("factor: expected constant or variable");

    } else if (s->kind == constant) {
      emit(1, 0, s->const_val);

    } else {
      emit(3, lex_level - s->level, s->m);
    }

    return;
  }

  t = next_token(numbersym, NULL);
  if (t) {
    emit(1, 0, atoi(t->lexeme.arr));
    return;
  }

  t = next_token(lparentsym, NULL);
  if (!t) {
    err("factor: expected identifier, number or left parentheses");
  }

  is_expression();
  t = next_token(rparentsym, "expression: expected right parentheses");
}

void is_term() {
  is_factor();

  // Match either multiplication or division.

  token *t;
  while ((t = next_token(multsym, NULL)) || (t = next_token(slashsym, NULL))) {
    is_factor();

    // Emit multiplication
    if (t->kind == multsym)
      emit(2, 0, 3);

    // Emit division
    if (t->kind == slashsym)
      emit(2, 0, 4);
  }
}

void is_expression() {
  is_term();

  token *t;
  while ((t = next_token(plussym, NULL)) || (t = next_token(minussym, NULL))) {
    is_term();

    if (t->kind == plussym)
      emit(2, 0, 1);

    if (t->kind == minussym)
      emit(2, 0, 2);
  }
}

int rel_ops[] = {eqsym, neqsym, lessym, leqsym, gtrsym, geqsym};
int rel_ops_m[] = {5, 6, 7, 8, 9, 10};
const int rel_ops_size = sizeof(rel_ops) / sizeof(rel_ops[0]);

int is_condition_odd() {
  token *t = next_token(oddsym, NULL);
  if (!t) {
    return 0;
  }

  is_expression();
  emit(2, 0, 11);

  return 1;
}

int is_condition_exp_rel() {
  is_expression();

  int rel_op_idx = -1;

  // Try all relational operators, return early if found
  for (int i = 0; i < rel_ops_size; i++)
    if (next_token(rel_ops[i], NULL)) {
      rel_op_idx = i;
      break;
    }

  if (rel_op_idx == -1)
    err("relational operator: expected one relational operator");

  is_expression();

  emit(2, 0, rel_ops_m[rel_op_idx]);

  return 1;
}

void is_condition() {
  if (is_condition_odd() || is_condition_exp_rel())
    return;

  err("condition: expected expression or odd statement");
}

int is_statement();

int is_statement_write() {
  token *t = next_token(writesym, NULL);
  if (!t)
    return 0;

  is_expression();
  emit(9, 0, 1);
  return 1;
}

int is_statement_read() {
  token *t = next_token(readsym, NULL);
  if (!t)
    return 0;

  emit(9, 0, 2);

  t = next_token(identsym, "read statement: expected identifier");

  symbol *s = find_symbol(t->lexeme.arr);

  if (!s || s->kind != variable)
    err("read statement: expected variable identifier");

  emit(4, lex_level - s->level, s->m);

  return 1;
}

int is_statement_while() {
  token *t = next_token(whilesym, NULL);
  if (!t)
    return 0;

  int condition_line = code_idx + 1;
  is_condition();

  int jpc_idx = emit(8, 0, 0);

  t = next_token(dosym, "end of condition: expected \"do\"");

  is_statement();

  // After statement, emit JMP that goes back to condition line
  emit(7, 0, condition_line);

  // Fix JPC condition to go to whatever's after the JMP line
  fix_jpc_jmp(jpc_idx);

  return 1;
}

int is_statement_if() {
  token *t = next_token(ifsym, NULL);
  if (!t)
    return 0;

  is_condition();

  int jpc_idx = emit(8, 0, 0);

  t = next_token(thensym, "end of condition: expected \"then\"");

  is_statement();

  fix_jpc_jmp(jpc_idx);

  t = next_token(fisym, "end of \"if\" block: expected \"fi\"");

  return 1;
}

int is_statement_begin() {
  token *t = next_token(beginsym, NULL);
  if (!t)
    return 0;

  do {

    is_statement();
  } while ((t = next_token(semicolonsym, NULL)) && t->kind == semicolonsym);

  t = next_token(endsym, "end of statements: expected \"end\"");

  return 1;
}

int is_statement_call() {
  token *t = next_token(callsym, NULL);
  if (!t)
    return 0;

  t = next_token(identsym, "procedure call: expected identifier");

  symbol *s = find_symbol(t->lexeme.arr);

  if (!s || s->kind != procedure)
    err("procedure call: could not find procedure with name");

  emit(5, lex_level - s->level, s->m * assembly_size);

  return 1;
}

int is_statement_becomes() {
  token *t = next_token(identsym, NULL);
  if (!t)
    return 0;

  symbol *s = find_symbol(t->lexeme.arr);

  if (!s || s->kind != variable)
    err("assignment: could not find any variable with name");

  t = next_token(becomessym, "assignment: expected \":=\" after identifier");

  is_expression();

  emit(4, lex_level - s->level, s->m);

  return 1;
}

// Array of functions that check for some kind of statement
int (*is_statement_arr[])(void) = {is_statement_becomes, is_statement_call,
                                   is_statement_begin,   is_statement_if,
                                   is_statement_while,   is_statement_read,
                                   is_statement_write};

int is_statement() {
  // Run each statement checker, break early if valid
  for (int i = 0; i < sizeof(is_statement_arr) / sizeof(is_statement_arr[0]);
       i++) {
    int (*fn)() = is_statement_arr[i];
    if (fn())
      return i;
  }
  return -1;
}

int is_var() {

  int variable_count = 0;

  token *t = next_token(varsym, NULL);
  if (!t)
    return variable_count;

  do {

    int offset = ar_min + variable_count;
    variable_count++;

    t = next_token(identsym, "expected identifier");

    symbol s;
    s.kind = variable;
    s.name = t->lexeme;
    s.level = lex_level;
    s.m = offset;

    push_symbol(&symbols, s);

  } while ((t = next_token(commasym, NULL)) && t->kind == commasym);

  t = next_token(semicolonsym, "expected \";\" after identifier");

  return variable_count;
}

void is_const() {
  token *t = next_token(constsym, NULL);
  if (!t)
    return;

  do {

    t = next_token(identsym, "expected identifier");
    token *identifier = t;
    symbol s;
    s.kind = constant;
    s.name = t->lexeme;
    s.level = lex_level;

    t = next_token(eqsym, "expected \"=\" after identifier");
    t = next_token(numbersym, "expected number after \"=\"");

    s.const_val = atoi(t->lexeme.arr);

    push_symbol(&symbols, s);

  } while ((t = next_token(commasym, NULL)) && t->kind == commasym);

  t = next_token(semicolonsym, "expected \";\" after identifier");
}

void is_block();

void is_procedure() {

  token *t;
  while ((t = next_token(proceduresym, NULL)) && t->kind == proceduresym) {

    t = next_token(identsym, "expected identifier after procedure");

    symbol s;
    s.name = t->lexeme;
    s.kind = procedure;
    s.level = lex_level;

    // Emit JMP
    int jmp_idx = emit(7, 0, 0);
    s.m = code_idx + 1;
    push_symbol(&symbols, s);

    t = next_token(semicolonsym, "expected \";\" after identifier");

    // Descend into and exit from new block
    is_block();

    // Emit RTN
    emit(2, 0, 0);

    // Fix jump to target whatever statement's after RTN.
    fix_jpc_jmp(jmp_idx);

    t = next_token(semicolonsym, "expected \";\" after block");
  }
  return;
}

void is_block() {

  lex_level++;
  int symbols_start = symbols.stored;

  is_const();                          // try to generate constants
  int variable_count = is_var();       // try to generate variables
  is_procedure();                      // try to generate procedure
  emit(6, 0, ar_min + variable_count); // emit INC

  // try to generate statements
  is_statement();

  // Remove any symbols generated by this block
  for (int i = symbols.stored - 1; symbols_start <= i && i < symbols.stored;
       i--)
    pop_symbol(&symbols);

  lex_level--;
}

void is_program() {
  is_block();
  token *t = next_token(periodsym, "expected \".\" after block");
  emit(9, 0, 3);
}

// Generate lexical error message
char *lex_err(token t) {
  // If identifier and too long
  if (t.kind == identsym && t.lexeme.stored > (iden_size + 1)) {
    return "identifier too long";
  }

  // If number and too long
  if (t.kind == numbersym && t.lexeme.stored > (number_size + 1)) {
    return "number too long";
  }

  // If otherwise invalid chars
  if (t.kind == 0) {
    return "not part of any lexeme";
  }

  return NULL;
}

// Check how many lex errors there are; print if also requested.
void lex_output(int also_print) {
  if (also_print) {
    printf("lexeme      | token | error\n");
    printf("------------+-------+------\n");
  }

  // For each stored token...
  for (int i = 0; i < tokens.stored; ++i) {
    token t = tokens.arr[i];

    // Possible error prefix
    char *err_prefix = "";

    // If any lex error, increase count of total errors
    char *err_msg = lex_err(t);
    if (err_msg) {
      lex_err_count++;
      err_prefix = "";
    } else {
      err_msg = "";
    }

    // Print lex analysis for current token
    if (also_print)
      printf("%-11s | %-5d | %s%s\n", t.lexeme.arr, t.kind, err_prefix,
             err_msg);
  }
}

void print_assembly(int flag, FILE *fptr) {

  if (!flag)
    return;

  if (flag == 1) {
    printf("Line | OP  | L | M\n");
    printf("-----+-----+---+---\n");
    for (int i = 0; i < asm_list.stored; i++) {
      assembly a = asm_list.arr[i];
      printf("%-4d | %-2s | %d | %d\n", i, a.pretty, a.l, a.m);
    }
    return;
  }

  if (flag == 2) {
    for (int i = 0; i < asm_list.stored; i++) {
      assembly a = asm_list.arr[i];
      fprintf(fptr, "%d %d %d\n", a.op, a.l, a.m);
    }

    fclose(fptr);
    return;
  }
}

int main(int argc, char *argv[]) {

  init_list((&asm_list));

  // Compile comment regex
  if (regcomp(&comment_rg.compiled, comment_rg.uncompiled, REG_EXTENDED)) {
    printf("Exiting since regex didn't compile: %s\n", comment_rg.uncompiled);
    return 1;
  }

  // Compile lexeme regexes, panic on error
  for (int i = 0; i < DEFINED_LEXEMES; ++i) {
    rg *lex_rg = &lex_rg_list[i];
    int err = regcomp(&lex_rg->compiled, lex_rg->uncompiled, REG_EXTENDED);
    if (err) {
      printf("Exiting since regex didn't compile: %s\n", lex_rg->uncompiled);
      return 1;
    }
  }

  // Check argument count
  if (argc < 2) {
    printf("Not enough arguments provided, exiting...\n");
    return 1;
  }

  // PL/0 input file ptr
  FILE *in_fptr = fopen(argv[1], "r");

  // Attempt to open PL/0 file
  if (!in_fptr) {
    printf("Error opening file %s\n", argv[1]);
    return 1;
  }

  // Copy PL/0 file input to memory
  for (char c = fgetc(in_fptr); c != EOF; c = fgetc(in_fptr)) {
    push_char(&input, c);
  }

  // Print source code
  printf("Source Program:\n%s\n", input.arr);
  // List of calculated tokens

  int line_row = 0;    // row where lexeme is located
  int line_column = 0; // column where lexeme is located

  // For each char in PL/0 input...
  for (int in_idx = 0; input.arr[in_idx] != '\0'; ++in_idx) {

    char *input_start = &input.arr[in_idx];
    char c = *input_start;

    // printf("%c", c);

    // Skip if non-printing character
    if (isspace(c)) {

      // Increment current line column
      line_column++;

      // If specifically newline, increment line row and reset line column
      if (input.arr[in_idx] == '\n') {
        line_column = 0;
        line_row++;
      }

      continue;
    }

    // Skip if comment
    int comment_length = is_comment(input_start);
    if (comment_length) {

      // Skip input by comment length, minus null terminator and amount
      // automatically skipped by char loop.
      in_idx += comment_length - 2;

      // Skip current line's column to char after comment's last char.
      line_column += comment_length;
      continue;
    }

    // Try to parse current input into valid lexeme for a new token
    token *new_token = parse_lexeme(input_start);
    if (new_token) {

      // Skip input by lexeme length, minus null terminator and amount
      // automatically skipped by char loop.
      in_idx += new_token->lexeme.stored - 2;

    } else {
      new_token = malloc(sizeof(token));
      push_char(&new_token->lexeme, c);
    }

    // Store where start of token was parsed from in source code
    new_token->row = line_row;
    new_token->col = line_column;

    // Skip line column by length of lexeme, minus null terminator
    line_column += new_token->lexeme.stored - 1;

    // Push new token
    push_token(&tokens, *new_token);
  }

  lex_output(0);

  printf("\n");

  // Immediately exit if any lexical analysis errors
  if (lex_err_count) {
    printf("Error: lexical analysis errors\n");
    return 1;
  }

  is_program();

  print_assembly(1, NULL);

  FILE *fptr = fopen("elf.txt", "w");
  print_assembly(2, fptr);
}
