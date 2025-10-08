from Token import Token, TokenType,lookup_ident
from typing import Any


class Lexer:
    def __init__(self, source: str) -> None:
        self.source = source
        self.position: int = -1
        self.read_position: int = 0
        self.line_no: int = 1
        self.current_char: str | None = None
        self.__read_char()

    def __read_char(self) -> None:
        if self.read_position >= len(self.source):
            self.current_char = None
        else:
            self.current_char = self.source[self.read_position]

        self.position = self.read_position
        self.read_position += 1

    def __peek_char(self)->str |None:
        if self.read_position>=len(self.source):
            return None
        return self.source[self.read_position]

    def __skip_whitespace(self) -> None:
        while self.current_char in [' ', '\t', '\n', '\r']:
            if self.current_char == '\n':
                self.line_no += 1
            self.__read_char()

    def __is_digit(self, ch: str) -> bool:
        return '0' <= ch <= '9'

    def __new_token(self, tt:TokenType,literal:Any)->Token:
        return Token(type=tt,literal=literal,line_no=self.line_no,position=self.position)
    
    def __is_letter(self,ch:str)-> bool:
        return 'a'<=ch and ch<='z' or 'A'<=ch and ch<='Z' or ch=='_'
    
    
    def __read_number(self) -> Token:
        start_pos: int = self.position
        dot_count: int = 0
        output: str = ""

        while self.current_char is not None and (self.__is_digit(self.current_char) or self.current_char == '.'):
            if self.current_char == '.':
                dot_count += 1
                if dot_count > 1:
                    print(f"Too many decimals at line {self.line_no}, position {self.position}")
                    return Token(TokenType.ILLEGAL, self.source[start_pos:self.position], self.line_no, start_pos)

            output += self.current_char
            self.__read_char()

        if self.current_char is not None and self.__is_letter(self.current_char):
            unit_start_pos = self.position
            while self.current_char is not None and self.__is_letter(self.current_char):
                self.__read_char()
            unit_part = self.source[unit_start_pos:self.position]

            valid_units = {"s", "ms", "us", "ns", "m", "h"}
            if unit_part in valid_units:
                return Token(TokenType.TIME, output + unit_part, self.line_no, start_pos)
            else:
                self.read_position = unit_start_pos
                self.position = self.read_position - 1
                self.__read_char() 

       
        if self.current_char == 'd':
            self.__read_char() 
            return Token(TokenType.DOUBLE, float(output), self.line_no, start_pos)

        if dot_count == 0:
            return Token(TokenType.INT, int(output), self.line_no, start_pos)
        else:
            return Token(TokenType.FLOAT, float(output), self.line_no, start_pos)
        
    def __read_identifier(self) ->str:
        position=self.position
        while self.current_char is not None and (self.__is_letter(self.current_char) or self.current_char.isalnum()):
            self.__read_char()
        return self.source[position:self.position]
    
    def next_token(self) -> Token:
        self.__skip_whitespace()

        if self.current_char == '@':
            while self.current_char is not None and self.current_char != '\n':
                self.__read_char()
            if self.current_char == '\n':
                self.__read_char()
                self.line_no += 1
            return self.next_token()

        if self.current_char is None:
            return Token(TokenType.EOF, "", self.line_no, self.position)

        match self.current_char:
            case '+':
                if self.__peek_char()=="=":
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.PLUS_EQ, ch+self.current_char)
                elif self.__peek_char()=="+":
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.PLUS_PLUS, ch+self.current_char)
                else:
                    tok = Token(TokenType.PLUS, self.current_char, self.line_no, self.position)
            
            case '-':
                peek = self.__peek_char()
                if peek == '=':
                    ch = self.current_char
                    self.__read_char()
                    tok = self.__new_token(TokenType.MINUS_EQ, ch + self.current_char)
                elif peek == '-':
                    ch = self.current_char
                    self.__read_char()
                    tok = self.__new_token(TokenType.MINUS_MINUS, ch + self.current_char)
                elif peek == '>':  
                    ch = self.current_char
                    self.__read_char()
                    tok = self.__new_token(TokenType.ARROW, ch + self.current_char)
                else:
                    tok = self.__new_token(TokenType.MINUS, self.current_char)


            case '*':
                if self.__peek_char()=="=":
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.MUL_EQ, ch+self.current_char)
                else:
                    tok = Token(TokenType.ASTERISK, self.current_char, self.line_no, self.position)
            case '.':
                tok = self.__new_token(TokenType.DOT, self.current_char)

            case '/':
                if self.__peek_char()=="=":
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.DIV_EQ, ch+self.current_char)
                else:
                    tok = Token(TokenType.SLASH, self.current_char, self.line_no, self.position)
            case '~':
                tok = self.__new_token(TokenType.TILDE, self.current_char)

            case '%':
                tok = Token(TokenType.MODULUS, self.current_char, self.line_no, self.position)
            case '^':
                tok = Token(TokenType.POW, self.current_char, self.line_no, self.position)
            case ',':
                tok=Token(TokenType.COMMA,self.current_char,self.line_no, self.position)
            case '"': 
                tok=Token(TokenType.STRING,self.__read_string(),self.line_no, self.position)
            case '&':
                if self.__peek_char() == '&':
                    ch = self.current_char
                    self.__read_char()
                    tok = self.__new_token(TokenType.AND, ch+self.current_char)
                else:
                    tok = self.__new_token(TokenType.ILLEGAL, self.current_char)

            case '|':
                if self.__peek_char() == '|':
                    ch = self.current_char
                    self.__read_char()
                    tok = self.__new_token(TokenType.OR, ch+self.current_char)
                else:
                    tok = self.__new_token(TokenType.PIPE, self.current_char)

            case '<':
                if self.__peek_char()=='=':
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.LT_EQ,ch+self.current_char)
                else:
                    tok=self.__new_token(TokenType.LT,self.current_char)
            case '>':
                if self.__peek_char()=='=':
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.GT_EQ,ch+self.current_char)
                else:
                    tok=self.__new_token(TokenType.GT,self.current_char)
            case '=':
                if self.__peek_char() =='=':
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.EQ_EQ,ch+self.current_char)
                else:
                    tok=self.__new_token(TokenType.EQ,self.current_char)
            case '!':
                if self.__peek_char()=='=':
                    ch=self.current_char
                    self.__read_char()
                    tok=self.__new_token(TokenType.NOT_EQ,ch+self.current_char)
                else:
                    tok=self.__new_token(TokenType.NOT,self.current_char)


            case ':':
                tok = Token(TokenType.COLON, self.current_char, self.line_no, self.position)
            
            case ';':
                tok = Token(TokenType.SEMICOLON, self.current_char, self.line_no, self.position)
            case '(':
                tok = Token(TokenType.LPAREN, self.current_char, self.line_no, self.position)
            case ')':
                tok = Token(TokenType.RPAREN, self.current_char, self.line_no, self.position)
            case '[':
                tok = Token(TokenType.LBRACKET, self.current_char, self.line_no, self.position)
            case ']':
                tok = Token(TokenType.RBRACKET, self.current_char, self.line_no, self.position)

            case _:
                if self.__is_letter(self.current_char):
                    literal:str=self.__read_identifier()
                    tt:TokenType=lookup_ident(literal)
                    tok=self.__new_token(tt=tt,literal=literal)
                    return tok
                if self.__is_digit(self.current_char):
                    return self.__read_number()
                else:
                    tok = Token(TokenType.ILLEGAL, self.current_char, self.line_no, self.position)

        self.__read_char()
        return tok
    
    def __read_string(self) -> str:
        position = self.position + 1
        escaped = False
        result = ""

        while True:
            self.__read_char()
            if self.current_char is None:
                break

            if escaped:
                if self.current_char == "n":
                    result += "\n"
                elif self.current_char == "t":
                    result += "\t"
                elif self.current_char == '"':
                    result += '"'
                else:
                    result += self.current_char
                escaped = False
            elif self.current_char == "\\":
                escaped = True
            elif self.current_char == '"':
                break
            else:
                result += self.current_char

        return result
