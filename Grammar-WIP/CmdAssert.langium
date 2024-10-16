grammar Smt

entry Model:
    commands+=Command+;

Command:
   CmdAssert
   ;

CmdAssert:
    PAR_OPEN 'assert' term=Term PAR_CLOSE;


SortedVar:
    PAR_OPEN symbol=SmtSymbol sort=Sort PAR_CLOSE;

Sort:
    identifier=Identifier | PAR_OPEN identifier=Identifier sorts+=Sort+ PAR_CLOSE;

Index:
    num=NUMERAL | symbol=SmtSymbol;

Identifier:
    symbol=SmtSymbol | (PAR_OPEN '_' symbol=SmtSymbol indices+=Index+ PAR_CLOSE);


Term:
    SpecConstant
    | QualIdentifier
    | PAR_OPEN qualId=QualIdentifier term+=Term+ PAR_CLOSE
    | PAR_OPEN 'let' PAR_OPEN varBinding+=VarBinding+ PAR_CLOSE term=Term PAR_CLOSE
    | QuantifiedTerm
    | PAR_OPEN 'match' term=Term PAR_OPEN matchCase+=MatchCase+ PAR_CLOSE
    | PAR_OPEN '!' term=Term attribute+=Attribute+ PAR_CLOSE
    ;
QuantifiedTerm:
    PAR_OPEN ('forall' | 'exists' ) PAR_OPEN sortedVar+=SortedVar+ PAR_CLOSE term=Term PAR_CLOSE;

MatchCase:
    PAR_OPEN pattern=Pattern term=Term PAR_CLOSE;

Pattern:
    symbol=SmtSymbol | (PAR_OPEN symbol=SmtSymbol symbols+=SmtSymbol+ PAR_CLOSE);

VarBinding:
    PAR_OPEN symbol=SmtSymbol term=Term PAR_CLOSE;

QualIdentifier:
    id=SIMPLE_SYMBOL;

SpecConstant returns string:
    NUMERAL | DECIMAL | HEXADECIMAL | BINARY | STRING;


SmtSymbol returns string:
    SIMPLE_SYMBOL;


Keyword:
    ':' simpleSymbol=SIMPLE_SYMBOL;

Attribute:
    keyWord=Keyword | keyWord=Keyword value=AttributeValue;

AttributeValue:
    const=SpecConstant 
    | symbol=SmtSymbol 
    | {infer AttributeValue} PAR_OPEN exprs+=SExpr* PAR_CLOSE;

SExpr infers SExpr:
    const=SpecConstant | symbol=SmtSymbol | keyWord = Keyword | PAR_OPEN exprs+=SExpr+ PAR_CLOSE;


// Lexer rules
terminal PAR_OPEN: '(';
terminal PAR_CLOSE: ')';
terminal BValue: 'true' | 'false';
terminal LETTER returns string: /[a-zA-Z]/;
terminal DIGIT returns number: /[0-9]/;
terminal NUMERAL returns number: /0|[0-9][0-9]*/;
terminal DECIMAL: NUMERAL '.' NUMERAL;
terminal HEXADECIMAL: /#x[0-9a-fA-F]+/;
terminal BINARY: /#b[01]+/;
terminal STRING returns string: /"([^"\\]|\\.|(WS|PRINTABLE_CHAR))+"/;
hidden terminal WS: /\s+/;


terminal SIMPLE_SYMBOL: 
    (LETTER | '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<' | '>' | '@')
    (LETTER | DIGIT | '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<' | '>' | '@')*;
hidden terminal SL_COMMENT: /;[^\n\r]*/;
terminal PRINTABLE_CHAR:  /[\u0020-\u007E\u0080-\u00FF]/;