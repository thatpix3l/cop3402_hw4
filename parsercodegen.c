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
  modsym,
  callsym,
  proceduresym
} token_kind;

char *op_codes[] = {"",    "LIT", "OPR", "LOD", "STO",
                    "CAL", "INC", "JMP", "JPC", "SYS"};

char *sys_subcodes[] = {"", "OUT", "INP", "EOP"};

char *opr_subcodes[] = {"RTN", "ADD", "SUB", "MUL", "DIV", "EQL",
                        "NEQ", "LSS", "LEQ", "GTR", "GEQ", "ODD"};

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
void char_pre_push(char_list *l) {

  // If no item in list, ignore.
  char *c = peek_char(l);
  if (!c)
    return;

  // If top item in list is not null, return
  if (*c != '\0')
    return;

  // Since top is nul terminator, decrement stored so next push overwrites NULL
  l->stored--;
}
void char_post_push(char_list *l) {
  l->arr[l->stored] = '\0';
  l->stored++;
}
new_list_manager(char, char_pre_push, char_post_push);

// Token generated from PL/0 source code.
typedef struct token {
  token_kind tk;    // token type
  char_list lexeme; // lexeme string used to detect type of token
  int row;          // input source line row start
  int col;          // input source line column start
  int l;            // symbol lexicographical level
  int m;            // symbol m
  int val;          // const/var value
  int op;           // op code
  symbol_kind sk;   // symbol kind
} token;

// Create a new basic list for token management.
new_list_type(token);
new_list_manager(token, ignore, ignore);

#define delim "([^a-zA-Z])"                   // don't match letters
#define uncom(reg) .uncompiled = "(^" reg ")" // match begin of line

// Regex wrapper; used for organization.
typedef struct rg {
  char *uncompiled; // uncompiled regex
  regex_t compiled; // compiled regex
} rg;

// Lexemes
rg lex_rg_list[] = {
    {uncom("odd") delim},                       // oddsym
    {uncom("[a-zA-Z]([a-zA-Z]|[0-9])*") delim}, // identsym
    {uncom("[0-9]([0-9])*")},                   // numbersym
    {uncom("\\+")},                             // plussym
    {uncom("\\-")},                             // minussym
    {uncom("\\*")},                             // multsym
    {uncom("\\/")},                             // slashsym
    {uncom("fi") delim},                        // fisym
    {uncom("=")},                               // eqsym
    {uncom("\\<>")},                            // neqsym
    {uncom("<")},                               // lessym
    {uncom("<=")},                              // leqsym
    {uncom(">")},                               // gtrsym
    {uncom(">=")},                              // geqsym
    {uncom("\\(")},                             // lparentsym
    {uncom("\\)")},                             // rparentsym
    {uncom(",")},                               // commasym
    {uncom(";")},                               // semicolonsym
    {uncom("\\.")},                             // periodsym
    {uncom(":=")},                              // becomessym
    {uncom("begin") delim},                     // beginsym
    {uncom("end") delim},                       // endsym
    {uncom("if") delim},                        // ifsym
    {uncom("then") delim},                      // thensym
    {uncom("while") delim},                     // whilesym
    {uncom("do") delim},                        // dosym
    {uncom("const") delim},                     // constsym
    {uncom("var") delim},                       // varsym
    {uncom("write") delim},                     // writesym
    {uncom("read") delim},                      // readsym
    {uncom("mod") delim},                       // modsym
    {uncom("call") delim},                      // callsym
    {uncom("procedure") delim}                  // proceduresym
};
#define DEFINED_LEXEMES sizeof(lex_rg_list) / sizeof(lex_rg_list[0])

// Regex to match a string starting with a comment.
rg comment_rg = {uncom("/\\*(.|\r|\n|\t|\v)*\\*/")};

// Parse lexeme using specific regex.
token *parse_lexeme_specific(char *s, int reg_idx) {

  regmatch_t submatches[2];                           // submatches
  regex_t *compiled = &lex_rg_list[reg_idx].compiled; // compiled regex

  // If can't match regex, exit early
  if (regexec(compiled, s, 2, submatches, 0))
    return NULL;

  // Only here if regex matches

  token *t = malloc(sizeof(token)); // malloc token
  t->tk = reg_idx;                  // regex used to match
  init_list((&t->lexeme));

  int match_length = submatches[1].rm_eo;

  // printf("match length: %d\n", match_length);

  // Set allocation stored size
  // t->lexeme.alloc = submatches[1].rm_eo + 1;
  // t->lexeme.stored = t->lexeme.alloc;

  // Allocate memory for lexeme name
  // t->lexeme.arr = calloc(t->lexeme.alloc, submatches[1].rm_eo);

  // Store lexeme name
  // printf("length: %d\n", submatches[1].rm_eo);
  for (int i = 0; i < match_length; i++) {
    char c = s[i];
    push_char(&t->lexeme, c);
    // printf("after push: %s\n", t->lexeme.arr);
    // t->lexeme.arr[i] = s[i];
  }

  // printf("string length: %d\n", t->lexeme.stored - 1);

  // Terminate
  // t->lexeme.arr[submatches[1].rm_eo] = '\0';

  return t;
}

char_list input;     // in-memory copy of PL/0 input
int tokens_idx = -1; // lexical token index
token_list tokens;   // lexical tokens
int lex_err_count;   // lexical error count
int lex_level = 0;   // lexical level

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

int code_line = 0;
token_list asm_list;

void fix_jpc(int idx) { asm_list.arr[idx].m = code_line + 1; }

int emit(int op_code, int l, int m) {
  code_line++;
  char *pretty_name;

  for (int i = 1; i < sizeof(sys_subcodes) / sizeof(sys_subcodes[0]); i++) {
    if (op_code == i) {
      pretty_name = sys_subcodes[i];
      break;
    }
  }

  for (int i = 0; i < sizeof(opr_subcodes) / sizeof(opr_subcodes[0]); i++) {
    if (op_code == i) {
      pretty_name = opr_subcodes[i];
      break;
    }
  }

  for (int i = 0; i < sizeof(op_codes) / sizeof(op_codes[0]); i++) {
    if (op_code == i) {
      pretty_name = op_codes[i];
      break;
    }
  }

  token t;
  t.op = op_code;
  t.l = l;
  t.m = m;
  t.lexeme.arr = pretty_name;

  push_token(&asm_list, t);
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

token *latest_token;
token_list const_var_procedure; // list of either const or var tokens

void print_consts_vars() {
  for (int i = 0; i < const_var_procedure.stored; i++) {
    printf("%s\n", const_var_procedure.arr[i].lexeme.arr);
  }
}

// Print message and panic.
void err(char *s) {

  // print_consts_vars();

  token *t = latest_token;
  if (!t) {
    printf("error: %s\n", s);
    return;
  }

  printf("line: %d, column: %d, lexeme: %s, regex: %s, error: %s\n", t->row + 1,
         t->col + t->lexeme.stored, t->lexeme.arr,
         lex_rg_list[t->tk].uncompiled, s);
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
  if (!t || t->tk != token_sym) {

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

token *find_symbol(char *s) {

  for (int i = const_var_procedure.stored - 1; i >= 0; i--) {

    token *stored_token = &const_var_procedure.arr[i];

    if (strcmp(s, stored_token->lexeme.arr) == 0)
      return stored_token;
  }

  return NULL;
}

void is_factor() {
  token *t;
  t = next_token(identsym, NULL);
  if (t) {

    token *s = find_symbol(t->lexeme.arr);

    if (!s) {
      err("identifier is not defined");
    }

    if (s->sk == procedure) {
      err("expected constant or variable, got procedure instead");

    } else if (s->sk == constant) {
      emit(1, 0, s->val);

    } else {
      emit(3, s->l, s->m);
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
    err("expected identifier, number or left parentheses");
  }

  is_expression();
  t = next_token(rparentsym, "expected right parentheses");
}

int term_ops[] = {multsym, slashsym, modsym};
int term_ops_m[] = {3, 4, 11};

void is_term() {
  is_factor();

  // Match either multiplication, division or modulus.
  for (int i = 0; i < sizeof(term_ops) / sizeof(term_ops[0]); i++) {
    token *t = next_token(term_ops[i], NULL);
    if (t) {
      emit(2, 0, term_ops_m[i]);
      return;
    }
  }
}

void is_expression() {

  is_term();

  token *t;
  while ((t = next_token(plussym, NULL)) || (t = next_token(minussym, NULL))) {
    is_term();

    if (t->tk == plussym)
      emit(2, 0, 1);

    if (t->tk == minussym)
      emit(2, 0, 2);
  }
}

int rel_ops[] = {eqsym, neqsym, lessym, leqsym, gtrsym, geqsym};
int rel_ops_m[] = {5, 6, 7, 8, 9, 10};

void is_rel_op() {
  token *t;
  // Try all relational operators, return early if found
  for (int i = 0; i < sizeof(rel_ops) / sizeof(rel_ops[0]); i++) {
    if ((t = next_token(rel_ops[i], NULL))) {
      emit(2, 0, rel_ops_m[i]);
      return;
    }
  }
  err("expected relational operator");
}

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
  is_rel_op();
  is_expression();
  return 1;
}

void is_condition() {
  if (is_condition_odd() || is_condition_exp_rel())
    return;

  err("expected odd condition or expression condition");
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

  t = next_token(identsym, "expected identifier after \"read\"");

  token *existing_symbol = find_symbol(t->lexeme.arr);

  if (!existing_symbol || existing_symbol->sk != variable)
    err("expected variable to store user input");

  emit(9, 0, 2);
  emit(4, existing_symbol->l, existing_symbol->m);

  return 1;
}

int is_statement_while() {
  token *t = next_token(whilesym, NULL);
  if (!t)
    return 0;

  int condition_line = code_line + 1;

  is_condition();

  t = next_token(dosym, "expected \"do\" after condition");

  int jpc_idx = emit(8, 0, 0);

  is_statement();

  emit(8, 0, condition_line);

  fix_jpc(jpc_idx);

  return 1;
}

int is_statement_if() {
  token *t = next_token(ifsym, NULL);
  if (!t)
    return 0;

  is_condition();

  int jpc_idx = emit(8, 0, 0);

  t = next_token(thensym, "expected \"then\" after condition");

  is_statement();

  fix_jpc(jpc_idx);

  t = next_token(fisym, "expected \"fi\" after statement");

  return 1;
}

int is_statement_begin() {
  token *t = next_token(beginsym, NULL);
  if (!t)
    return 0;

  do {
    is_statement();
  } while ((t = next_token(semicolonsym, NULL)) && t->tk == semicolonsym);

  t = next_token(endsym, "expected \"end\" after statement");

  return 1;
}

int is_statement_call() {
  token *t = next_token(callsym, NULL);
  if (!t)
    return 0;

  t = next_token(identsym, "expected identifier after \"call\"");

  for (int i = const_var_procedure.stored - 1; i >= 0; i--) {
    token *s = &const_var_procedure.arr[i];
    if (strcmp(t->lexeme.arr, s->lexeme.arr) == 0) {

      if (s->sk != procedure)
        err("attempt to call symbol that is not a procedure");

      emit(5, s->l, s->m);
      return 1;
    }
  }

  err("attempt to call non-existent procedure");

  return 0;
}

int is_statement_becomes() {
  token *t = next_token(identsym, NULL);
  if (!t)
    return 0;

  token *s = find_symbol(t->lexeme.arr);

  if (!s)
    err("could not find symbol with name");

  if (s->sk != variable)
    err("attempt to assign to non-variable symbol");

  t = next_token(becomessym, "expected \":=\" after identifier");

  is_expression();

  emit(4, t->l, t->m);

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
  int var_count;

  token *t = next_token(varsym, NULL);
  if (!t)
    return var_count;

  int m = ar_min;

  do {

    var_count++;
    m++;

    t = next_token(identsym, "expected identifier");

    t->sk = variable;
    t->l = lex_level;
    t->m = m;
    push_token(&const_var_procedure, *t);

  } while ((t = next_token(commasym, NULL)) && t->tk == commasym);

  t = next_token(semicolonsym, "expected \";\" after identifier");

  return var_count;
}

void is_const() {
  token *t = next_token(constsym, NULL);
  if (!t)
    return;

  do {

    t = next_token(identsym, "expected identifier");
    token *identifier = t;

    t = next_token(eqsym, "expected \"=\" after identifier");
    t = next_token(numbersym, "expected number after \"=\"");

    identifier->sk = constant;
    identifier->val = atoi(t->lexeme.arr);
    push_token(&const_var_procedure, *identifier);

  } while ((t = next_token(commasym, NULL)) && t->tk == commasym);

  t = next_token(semicolonsym, "expected \";\" after identifier");
}

void is_block();

void is_procedure() {

  token *t;
  while ((t = next_token(proceduresym, NULL)) && t->tk == proceduresym) {

    t = next_token(identsym, "expected identifier after procedure");
    t->sk = procedure;
    t->l = lex_level;
    t->m = lex_level;
    push_token(&const_var_procedure, *t);

    t = next_token(semicolonsym, "expected \";\" after identifier");

    lex_level++;
    is_block();

    // Remove any constants/variables/procedures generated by the block
    for (int i = const_var_procedure.stored - 1; i >= 0; i--) {
      token *top = peek_token(&asm_list);
      int is_const_var_proc =
          top->sk == constant || top->sk == variable || top->sk == procedure;
      if (top && is_const_var_proc && top->l == lex_level)
        pop_token(&const_var_procedure);
    }

    lex_level--;

    t = next_token(semicolonsym, "expected \";\" after block");
  }
}

void is_block() {
  is_const();
  is_var();
  is_procedure();
  is_statement();
}

void is_program() {
  is_block();
  token *t = next_token(periodsym, "expected \".\" after block");
  emit(9, 0, 3);
}

// Generate lexical error message
char *lex_err(token t) {
  // If identifier and too long
  if (t.tk == identsym && t.lexeme.stored > (iden_size + 1)) {
    return "identifier too long";
  }

  // If number and too long
  if (t.tk == numbersym && t.lexeme.stored > (number_size + 1)) {
    return "number too long";
  }

  // If otherwise invalid chars
  if (t.tk == 0) {
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
      printf("%-11s | %-5d | %s%s\n", t.lexeme.arr, t.tk, err_prefix, err_msg);
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

  lex_output(1);

  printf("\n");

  // Immediately exit if any lexical analysis errors
  if (lex_err_count) {
    printf("Error: lexical analysis errors\n");
    return 1;
  }

  is_program();

  for (int i = 0; i < asm_list.stored; i++) {
    token t = asm_list.arr[i];
    printf("%s %2d %2d\n", t.lexeme.arr, t.l, t.m);
  }
}
