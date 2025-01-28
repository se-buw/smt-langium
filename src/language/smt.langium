grammar Smt

entry Model:
    commands+=Command+;


Command:
    CmdAssert
   | PAR_OPEN basicCommand=BasicCommand PAR_CLOSE
   | CmdCheckSat
   | CmdConstDecl
   | CmdDecDataType
   | CmdDecDataTypes
   | CmdFunDecl
   | CmdSortDeclZ3
   | CmdDefSort
   | CmdDefFun
   | CmdDefFunsRec
   | PAR_OPEN 'echo' STRING PAR_CLOSE
   | PAR_OPEN 'get-info' infoFlag=InfoFlag PAR_CLOSE
   | PAR_OPEN 'get-option' name=Keyword PAR_CLOSE
   | PAR_OPEN 'get-value' PAR_OPEN term+=Term+ PAR_CLOSE PAR_CLOSE
   | PAR_OPEN 'pop' NUMERAL* PAR_CLOSE // '*' for Z3
   | PAR_OPEN 'push' NUMERAL* PAR_CLOSE // '*' for Z3
   | PAR_OPEN 'set-info' name=Attribute PAR_CLOSE
   | PAR_OPEN 'set-logic' symbol=SmtSymbol PAR_CLOSE
   | PAR_OPEN 'set-option' option=Option PAR_CLOSE
    // Z3 Commands
   | PAR_OPEN 'eval' term+=Term+ PAR_CLOSE
   | PAR_OPEN ('maximize' | 'minimize') term=Term PAR_CLOSE
;

CmdCheckSat:
    PAR_OPEN 'check-sat' PAR_CLOSE
    | PAR_OPEN 'check-sat-assuming' PAR_OPEN propLiteral+=Term* PAR_CLOSE PAR_CLOSE //Support Z3, SMT-LIB: PropLiteral
;

CmdAssert:
    PAR_OPEN 'assert' term=Term PAR_CLOSE;

BasicCommand returns string:
    'check-sat' | 'reset' | 'reset-assertions' | 'get-model' | 'exit'
    | 'get-assertions' | 'get-assignment' | 'get-proof' | 'get-unsat-assumptions'
    | 'get-unsat-core';


// HERE
// HERE
// Create a Union Types for commands declaring elements with a name
type NamedElement = CmdConstDecl | CmdFunDecl | FunctionDef | FunctionDec | SortedVar; // sorted var is for inner functions
type NamedSort = CmdSortDeclZ3 | SortDec | SortDecZ3 | CmdDecDataType | CmdDefSort | SortedParameter;


CmdDefSort:
    PAR_OPEN commandType='define-sort' name=SmtSymbol PAR_OPEN symbol+=SortedParameter* PAR_CLOSE Sort PAR_CLOSE;

SortedParameter:
    name=(SmtSymbol|PreDefinedSort);

CmdSortDeclZ3:
    PAR_OPEN commandType='declare-sort' name=SmtSymbol number=NUMERAL* PAR_CLOSE; // SMT-LIB: '*' for z3

CmdConstDecl:
    PAR_OPEN commandType='declare-const' name=SmtSymbol sorts+=Sort+ PAR_CLOSE;

CmdFunDecl:
    PAR_OPEN commandType='declare-fun' name=SmtSymbol PAR_OPEN paramSorts+=Sort* PAR_CLOSE returnSort=Sort PAR_CLOSE;

CmdDefFun:
    PAR_OPEN commandType=DefFunCommandName FunctionDef PAR_CLOSE;

// CmdDefFunRec:
//     PAR_OPEN commandType='define-fun-rec' FunctionDef PAR_CLOSE;

// terminal DEFINE_FUN_REC: 'define-fun-rec';
// terminal DEFINE_FUN: 'define-fun';

// DefFunCommandName returns string:
//     DEFINE_FUN_REC | DEFINE_FUN;

DefFunCommandName returns string:
    'define-fun-rec'|'define-fun';



CmdDefFunsRec:
    PAR_OPEN commandType='define-funs-rec' PAR_OPEN functionDec+=FunctionDec+ PAR_CLOSE PAR_OPEN term+=Term+ PAR_CLOSE PAR_CLOSE;


CmdDecDataType:
    PAR_OPEN commandType='declare-datatype' name=SmtSymbol (dataTypeDec=DataTypeDec | dataTypeDec=DataTypeDecZ3) PAR_CLOSE; //Z3 variant


// sortDec is not exposed to other commands
// We only have access to it, if we stay inside the command, like an inner function
CmdDecDataTypes:
    PAR_OPEN commandType='declare-datatypes' 
    PAR_OPEN  sortDec+=SortDec+ PAR_CLOSE 
    PAR_OPEN dataTypeDecs+=CommonDataTypeDec+ PAR_CLOSE 
    PAR_CLOSE;

CommonDataTypeDec:
    DataTypeDec | DataTypeDecZ3;

DataTypeDec:
    PAR_OPEN constructorDecs+=ConstructorDec+ PAR_CLOSE
    | PAR_OPEN 'par' PAR_OPEN symbol+=SmtSymbol+ PAR_CLOSE PAR_OPEN constructorDecs+=ConstructorDec+ PAR_CLOSE PAR_CLOSE;

ConstructorDec:
    PAR_OPEN name=SmtSymbol selectorDec+=SelectorDec* PAR_CLOSE;

SelectorDec:
    PAR_OPEN name=SmtSymbol sort=Sort PAR_CLOSE 
    | PAR_OPEN listKey=('tail'|'head') sort=Sort PAR_CLOSE
;

SortDec:
    PAR_OPEN name=SmtSymbol num=NUMERAL PAR_CLOSE 
    | name=SmtSymbol;

FunctionDef:
    name=SmtSymbol PAR_OPEN sortedVars+=SortedVar* PAR_CLOSE Sort Term;

FunctionDefRec:
    name=SmtSymbol PAR_OPEN sortedVars+=SortedVar* PAR_CLOSE Sort Term;

FunctionDec:
    PAR_OPEN name=SmtSymbol PAR_OPEN vars+=SortedVar* PAR_CLOSE Sort PAR_CLOSE;

SortedVar:
    PAR_OPEN name=SmtSymbol sort=Sort PAR_CLOSE;

Sort:
    identifier=SortIdentifier 
    | PAR_OPEN identifier=SortIdentifier sorts+=Sort+ PAR_CLOSE
;

Index:
    num=NUMERAL | symbol=SmtSymbol;

SortIdentifier:
    ID=[NamedSort:SmtSymbol] 
    | (PAR_OPEN '_' ID=[NamedSort:SmtSymbol] indices+=Index+ PAR_CLOSE)
    | PreDefinedSort
    | 'Array'
;



PreDefinedSort:
    //sort=PREDEF_SORT;
    ID=('Int' | 'Bool' | 'Real' | 'List');

Term:
    SpecConstant
    | QualIdentifier
    | BValue
    | AttributedTerm
    | PAR_OPEN Operator term+=Term+ PAR_CLOSE 
    | PAR_OPEN 'if' term+=Term+ statement+=ConditionalTerm*  PAR_CLOSE
    | PAR_OPEN qualId=QualIdentifier term+=Term+  boolean=BValue? PAR_CLOSE
    | PAR_OPEN 'let' PAR_OPEN varBinding+=VarBinding+ PAR_CLOSE term=Term PAR_CLOSE
    | QuantifiedTerm
    | PAR_OPEN 'match' term=Term PAR_OPEN matchCase+=MatchCase+ PAR_CLOSE
    // | PAR_OPEN '!' term=Term attribute+=Attribute+ PAR_CLOSE
    | PAR_OPEN PAR_OPEN '_' (PSEUDO_BOOL_KEYWORD | CARDINALITY_KEYWORD)  NUMERAL* PAR_CLOSE SmtSymbol* PAR_CLOSE
    | PAR_OPEN PAR_OPEN '_' 'is' 'nil' PAR_CLOSE SmtSymbol* PAR_CLOSE // THIS IS TO REMOVE ERRORS
    | PAR_OPEN listKey=('tail'| 'head') term+=Term+ PAR_CLOSE
;

terminal PSEUDO_BOOL_KEYWORD: 'pbeq' | 'pbge' | 'pble';
terminal CARDINALITY_KEYWORD: 'at-least' | 'at-most';


QuantifiedTerm:
    PAR_OPEN ('forall' | 'exists' ) PAR_OPEN sortedVar+=SortedVar+ PAR_CLOSE term=(Term|PatternedTerm) PAR_CLOSE;

PatternedTerm:
    PAR_OPEN '!' bodyterm=Term patternAttribute+=PatternAttribute+  PAR_CLOSE;

PatternAttribute:
    ':pattern' PAR_OPEN term+=Term+ PAR_CLOSE;

ConditionalTerm:
    (SpecConstant|BValue) term+=Term+;

AttributedTerm:
    PAR_OPEN '!' term=Term ':named' name=SmtSymbol PAR_CLOSE;

MatchCase:
    PAR_OPEN pattern=Pattern term=Term PAR_CLOSE;

Pattern:
    symbol=SmtSymbol | (PAR_OPEN symbol=SmtSymbol symbols+=SmtSymbol+ PAR_CLOSE);

VarBinding:
    PAR_OPEN symbol=SmtSymbol term=Term PAR_CLOSE;

QualIdentifier:
    ID=[NamedElement:SmtSymbol];

SpecConstant returns string:
    NUMERAL | DECIMAL | HEXADECIMAL | BINARY | STRING;


SmtSymbol returns string:
    SIMPLE_SYMBOL;

Operator returns string:
    ARITHMETIC_OPERATOR | BOOLEAN_OPERATOR;

InfoFlag:
    ':' 'all-statistics' | ':' 'assertion-stack-levels' | ':' 'authors'
    | ':' 'error-behavior' | ':' 'name' | ':' 'reason-unknown'
    | ':' 'version' | Keyword;

Keyword:
    ':' symbol=SmtSymbol;

Attribute:
    keyWord=Keyword | keyWord=Keyword value=AttributeValue;

AttributeValue:
    const=SpecConstant 
    | symbol=SmtSymbol string+=STRING*
    | {infer AttributeValue} PAR_OPEN exprs+=SExpr* PAR_CLOSE;

SExpr infers SExpr:
    const=SpecConstant | symbol=SmtSymbol | keyWord=Keyword | PAR_OPEN exprs+=SExpr+ PAR_CLOSE;


Option:
    OptionTerminal | Attribute;

OptionTerminal returns string:
    ':' 'diagnostic-output-channel' STRING
    | ':' 'global-declarations' BValue
    | ':' 'interactive-mode' BValue
    | ':' 'print-success' BValue
    | ':' 'produce-assertions' BValue
    | ':' 'produce-assignments' BValue
    | ':' 'produce-models' BValue
    | ':' 'produce-proofs' BValue
    | ':' 'produce-unsat-assumptions' BValue
    | ':' 'produce-unsat-cores' BValue
    | ':' 'random-seed' NUMERAL
    | ':' 'regular-output-channel' STRING
    | ':' 'reproducible-resource-limit' NUMERAL
    // Z3 
    | ':' 'smt-auto-config' BValue
    | ':smt.mbqi' BValue
    | ':' 'smt.macro-finder' BValue
    | ':' 'model.compact' BValue
    | ':' 'opt.priority' SIMPLE_SYMBOL // Check
    | ':' 'pp.bv-literals' BValue
    | ':' 'verbosity' NUMERAL
;

// Z3 Related Specification
SortDecZ3:
    symbol+=SmtSymbol+;

ConstructorDecZ3:
    symbol=SmtSymbol selectorDec+=SelectorDecZ3*;

DataTypeDecZ3:
    PAR_OPEN constructorDecs+=ConstructorDecZ3+ PAR_CLOSE;

SelectorDecZ3:
    PAR_OPEN name=SmtSymbol sort+=Sort* PAR_CLOSE;

// Lexer rules
terminal PAR_OPEN: '(';
terminal PAR_CLOSE: ')';
terminal BValue: 'true' | 'false';
terminal LETTER returns string: /[a-zA-Z]/;
terminal DECIMAL: NUMERAL '.' NUMERAL;
terminal NUMERAL returns number: /0|[0-9][0-9]*/;
terminal DIGIT returns number: /[0-9]/;
terminal HEXADECIMAL: /#x[0-9a-fA-F]+/;
terminal BINARY: /#b[01]+/;
terminal STRING returns string: /"([^"\\]|\\.|(WS|PRINTABLE_CHAR))+"/;
hidden terminal WS: /\s+/;

terminal PREDEF_SORT: 'Bool' | 'Int' | 'Real' | 'List';
// - + * / div mod abs <= < >= > to_real to_int is_int
terminal ARITHMETIC_OPERATOR: '-' | '+' | '*' | '/' | 'div' | 'mod' | 'abs' | '<=' | '<' | '>=' | '>'; 
// not => and or xor = // distinct ite
terminal BOOLEAN_OPERATOR: 'not' | '=>' | 'and' | 'or' | 'xor' | '=' | 'ite' | 'distinct';

terminal SIMPLE_SYMBOL: 
    (LETTER | '+' | '-' | '/' | '*' | ',' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<' | '>' | '@')
    (LETTER | DIGIT | '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<' | '>' | '@')*;
hidden terminal SL_COMMENT: /;[^\n\r]*/;
