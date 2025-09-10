from enum import Enum
from typing import Any

class TokenType(Enum):
    EOF="EOF"
    ILLEGAL="ILLEGAL"

    INT="INT"
    FLOAT="FLOAT"
    DOUBLE="DOUBLE"
    IDENTIFIER="IDENTIFIER"
    STRING="STRING"
    NULL = "NULL"

    PLUS="PLUS"
    MINUS="MINUS"
    ASTERISK="ASTERISK"
    SLASH="SLASH"
    POW="POW"
    MODULUS="MODULUS"

    EQ="EQ"
    LT='<'
    GT='>'
    EQ_EQ='=='
    NOT_EQ='!='
    LT_EQ='<='
    GT_EQ='>='
    DOT='.'

    PLUS_EQ="PLUS_EQ"
    MINUS_EQ="MINUS_EQ"
    DIV_EQ="DIV_EQ"
    MUL_EQ="MUL_EQ"


    COLON="COLON"
    COMMA="COMMA"
    SEMICOLON="SEMICOLON"
    LPAREN="LPAREN"
    RPAREN="RPAREN"
    LBRACE="LBRACE"
    RBRACE="RBRACE"
    LBRACKET="LBRACKET"
    RBRACKET="RBRACKET"

    PLUS_PLUS="PLUS_PLUS"
    MINUS_MINUS="MINUS_MINUS"

    # Keywords
    VAR = "VAR"
    FUN = "FUN"
    NUF = "NUF"
    IF = "IF"
    ELIF = "ELIF"
    ELSE = "ELSE"
    ESLE="ESLE"
    FI = "FI"
    FOR = "FOR"
    ROF = "ROF"
    WHILE = "WHILE"
    ELIHW = "ELIHW"
    RETURN = "RETURN"
    BREAK = "BREAK"
    CONTINUE = "CONTINUE"
    TRUE = "TRUE"
    FALSE = "FALSE"
    
    STRUCT = "STRUCT"
    TCURTS="TCURTS"
    IMPORT = "IMPORT"
    ASYNC = "ASYNC"
    AWAIT = "AWAIT"
    FROM = "FROM"
    LOAD="LOAD"
    INPUT="INPUT"
    ARRAY="ARRAY"
    RESERVE="RESERVE"
    FREE="FREE"
    CLASS="CLASS"
    SSALC="SSALC"
    THIS="THIS"
    REF="REF"
    DEREF="DEREF"
    REWIND="REWIND"
    FASTFORWARD="FASTFORWARD"
    BRANCH="BRANCH"
    HANDLE="HANDLE"
    END="END"
    FORK="FORK"
    MERGE="MERGE"
    OR="OR"
    AND="AND"
    NOT="NOT"
    QUBIT="QUBIT"
    MEASURE="MEASURE"
    RESET="RESET"
    PIPE="|"
    SNAPSHOT="SNAPSHOT"
    RESTORE="RESTORE"
    

    


    #Typing
    TYPE="TYPE"
    INT_TYPE = "INT_TYPE"
    FLOAT_TYPE = "FLOAT_TYPE"
    BOOL_TYPE = "BOOL_TYPE"
    STRING_TYPE = "STRING_TYPE"

class Token:
    def __init__(self, type: TokenType, literal: Any, line_no: int, position: int) -> None:
        self.type = type
        self.literal = literal
        self.line_no = line_no
        self.position = position

    def __str__(self) -> str:
        return f"Token[{self.type}:{self.literal}: Line {self.line_no}: Position {self.position}]"
    
    def __repr__(self)->str:
        return str(self)
    
KEYWORDS: dict[str,TokenType]={
    "var":TokenType.VAR,
    "fun": TokenType.FUN,
    "nuf": TokenType.NUF,
    "if": TokenType.IF,
    "elif": TokenType.ELIF,
    "else": TokenType.ELSE,
    "esle": TokenType.ESLE,
    "fi": TokenType.FI,
    "for": TokenType.FOR,
    "rof": TokenType.ROF,
    "while": TokenType.WHILE,
    "elihw": TokenType.ELIHW,
    "return": TokenType.RETURN,
    "break": TokenType.BREAK,
    "continue": TokenType.CONTINUE,
    "True": TokenType.TRUE,
    "False": TokenType.FALSE,
    "null": TokenType.NULL,
    "struct": TokenType.STRUCT,
    "tcurts":TokenType.TCURTS,
    "import": TokenType.IMPORT,
    "async": TokenType.ASYNC,
    "await": TokenType.AWAIT,
    "from": TokenType.FROM,
    "load":TokenType.LOAD,
    "input": TokenType.INPUT,
    "array":TokenType.ARRAY,
    "reserve":TokenType.RESERVE,
    "free":TokenType.FREE,
    "class":TokenType.CLASS,
    "ssalc":TokenType.SSALC,
    "this":TokenType.THIS,
    "ref":TokenType.REF,
    "deref": TokenType.DEREF,
    "rewind":TokenType.REWIND,
    "fastforward":TokenType.FASTFORWARD,
    "branch":TokenType.BRANCH,
    "handle":TokenType.HANDLE,
    "end":TokenType.END,
    "fork":TokenType.FORK,
    "merge":TokenType.MERGE,
    "or":TokenType.OR,
    "qubit":TokenType.QUBIT,
    "measure":TokenType.MEASURE,
    "reset": TokenType.RESET,
    "snapshot":TokenType.SNAPSHOT,
    "restore":TokenType.RESTORE,

    
    
}
ALT_KEYWORDS: dict[str,TokenType]={
    "let": TokenType.VAR,
    "define": TokenType.FUN,
    "endfun": TokenType.NUF,
    "endfor": TokenType.ROF,
    "endwhile": TokenType.ELIHW,
}

TYPE_KEYWORDS:list[str]=["int","float","str","void"]

def lookup_ident(ident:str)->TokenType:
    tt:TokenType| None=KEYWORDS.get(ident)
    if tt is not None:
        return tt
    tt:TokenType| None=ALT_KEYWORDS.get(ident)
    if tt is not None:
        return tt
    if ident in TYPE_KEYWORDS:
        return TokenType.TYPE
    return TokenType.IDENTIFIER