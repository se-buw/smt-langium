grammar Smt

entry Model:
    commands+=Command+;

Command:
    CmdDecDataTypes;
    

CmdDecDataTypes:
    PAR_OPEN 'declare-datatypes' PAR_OPEN (
        sortDecZ3+=SortDecZ3* PAR_CLOSE PAR_OPEN dataTypeDecZ3+=DataTypeDecZ3+
        | sortDec+=SortDec+ PAR_CLOSE PAR_OPEN dataTypeDec+=DataTypeDec+
    ) PAR_CLOSE PAR_CLOSE;

// Z3 Related
SortDecZ3:
    symbol+=SmtSymbol+;

ConstructorDecZ3:
    symbol=SmtSymbol selectorDec+=SelectorDecZ3*;

DataTypeDecZ3:
    PAR_OPEN constructorDecs+=ConstructorDecZ3+ PAR_CLOSE;

SelectorDecZ3:
    PAR_OPEN symbol=SmtSymbol sort+=Sort* PAR_CLOSE;

SortDec:
    PAR_OPEN symbol=SmtSymbol num=NUMERAL PAR_CLOSE;

DataTypeDec:
    PAR_OPEN constructorDecs+=ConstructorDec+ PAR_CLOSE
    | PAR_OPEN 'par' PAR_OPEN symbol+=SmtSymbol+ PAR_CLOSE PAR_OPEN constructorDecs+=ConstructorDec+ PAR_CLOSE PAR_CLOSE;
ConstructorDec:
    PAR_OPEN symbol=SmtSymbol selectorDec+=SelectorDec* PAR_CLOSE;

SelectorDec:
    PAR_OPEN symbol=SmtSymbol sort=Sort PAR_CLOSE;

Sort:
    identifier=Identifier | PAR_OPEN identifier=Identifier sorts+=Sort+ PAR_CLOSE;
SmtSymbol returns string:
    SIMPLE_SYMBOL;
Index:
    num=NUMERAL | symbol=SmtSymbol;

Identifier:
    symbol=SmtSymbol | (PAR_OPEN '_' symbol=SmtSymbol indices+=Index+ PAR_CLOSE);

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
